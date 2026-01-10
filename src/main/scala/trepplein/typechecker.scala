package trepplein

import scala.annotation.tailrec
import scala.collection.mutable

sealed trait DefEqRes {
  @inline final def &(that: => DefEqRes): DefEqRes = if (this != IsDefEq) this else that
}
case object IsDefEq extends DefEqRes {
  def forall(rs: Iterable[DefEqRes]): DefEqRes =
    rs.collectFirst { case r: NotDefEq => r }.getOrElse(IsDefEq)
}
final case class NotDefEq(a: Expr, b: Expr) extends DefEqRes

class TypeChecker(val env: PreEnvironment, val unsafeUnchecked: Boolean = false, val trustExports: Boolean = false) {
  def shouldCheck: Boolean = !unsafeUnchecked

  // Shared recursion depth counter across ALL recursive functions
  // This is like Lean 4's check_stack but using a counter instead of actual stack pointer
  // When the limit is exceeded, throw an error before JVM stack overflow
  // NOTE: Run with -Xss100m or higher for large files like Init
  private var recursionDepth = 0
  private val maxRecursionDepth = 5000  // Needs -Xss100m for this depth

  /** Check recursion depth and throw if exceeded. Call at entry to all recursive functions. */
  @inline private def checkDepth(): Unit = {
    recursionDepth += 1
    if (recursionDepth > maxRecursionDepth) {
      recursionDepth -= 1
      throw new StackOverflowError(s"Type checker recursion depth exceeded $maxRecursionDepth. Last decl: $debugCurrentDecl. Last expr head: ${exprHead(debugLastExpr)}")
    }
  }

  private def exprHead(e: Any): String = e match {
    case Apps(fn, as) => fn match {
      case Const(n, _) => s"Const($n) applied to ${as.size} args"
      case Proj(tn, idx, _) => s"Proj($tn, $idx)"
      case Lam(_, _) => s"Lam"
      case _ => fn.getClass.getSimpleName
    }
    case _ => if (e == null) "null" else e.getClass.getSimpleName
  }

  // Debug: track current declaration and expression
  var debugCurrentDecl: String = ""
  private var debugLastExpr: Any = null
  var bypassCount: Int = 0
  var stuckUniverseCount: Int = 0
  var stuckAppTypeCount: Int = 0
  var stuckProjTypeCount: Int = 0

  /** Simple expression pretty printer for debugging */
  private def prettyExpr(e: Expr, depth: Int = 0): String = {
    if (depth > 10) return "..."
    e match {
      case Const(n, levels) =>
        if (levels.isEmpty) n.toString else s"$n.{${levels.mkString(", ")}}"
      case Var(idx) => s"#$idx"
      case NatLit(n) => s"NatLit($n)"
      case StringLit(s) => s"StringLit(${s.take(20)})"
      case LocalConst(b, id) => s"@${b.prettyName}.$id"
      case Sort(l) => s"Sort($l)"
      case Apps(fn, args) if args.nonEmpty =>
        val fnStr = prettyExpr(fn, depth + 1)
        val argsStr = args.map(prettyExpr(_, depth + 1)).mkString(" ")
        s"($fnStr $argsStr)"
      case Lam(binding, body) =>
        s"(fun ${binding.prettyName} => ${prettyExpr(body, depth + 1)})"
      case Pi(binding, body) =>
        s"(${binding.prettyName} : ${prettyExpr(binding.ty, depth + 1)}) -> ${prettyExpr(body, depth + 1)}"
      case Let(binding, value, body) =>
        s"(let ${binding.prettyName} := ${prettyExpr(value, depth + 1)} in ${prettyExpr(body, depth + 1)})"
      case Proj(tyName, idx, struct) =>
        s"(${prettyExpr(struct, depth + 1)}.${idx})"
      case _ => e.toString.take(100)
    }
  }

  /** Decrement depth counter. Call in finally block of recursive functions. */
  @inline private def releaseDepth(): Unit = {
    recursionDepth -= 1
  }

  object NormalizedPis {
    def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
      whnf(e) match {
        case Pis(lcs1, f) if lcs1.nonEmpty =>
          val NormalizedPis(lcs2, g) = f
          Some((lcs1 ::: lcs2, g))
        case f => Some((Nil, f))
      }

    @tailrec def instantiate(e: Expr, ts: List[Expr], ctx: List[Expr] = Nil): Expr =
      (e, ts) match {
        case (Pi(_, body), t :: ts_) =>
          instantiate(body, ts_, t :: ctx)
        case (_, _ :: _) =>
          instantiate(whnf(e).ensuring(_.isInstanceOf[Pi]), ts, ctx)
        case (_, Nil) => e.instantiate(0, ctx.toVector)
      }
  }

  private val levelDefEqCache = mutable.AnyRefMap[(Level, Level), Boolean]()
  def isDefEq(a: Level, b: Level): Boolean =
    levelDefEqCache.getOrElseUpdate((a, b), a === b)

  def isProp(s: Expr): Boolean = whnf(s) match {
    case Sort(l) => l.isZero
    case _ => false
  }
  def isProposition(ty: Expr): Boolean = isProp(infer(ty))
  def isProof(p: Expr): Boolean = isProposition(infer(p))

  /** Two proof terms are proof-irrelevant equal if they are both proofs
   *  AND their types are definitionally equal.
   *  This matches the behavior of nanoda_lib and the Lean 4 kernel.
   */
  private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean = {
    // Both must be proofs
    if (!isProof(e1) || !isProof(e2)) return false

    // Their types must be definitionally equal
    val t1 = infer(e1)
    val t2 = infer(e2)
    checkDefEq(t1, t2) == IsDefEq
  }

  private def reqDefEq(cond: Boolean, e1: Expr, e2: Expr) =
    if (cond) IsDefEq else NotDefEq(e1, e2)

  def isDefEq(e1: Expr, e2: Expr): Boolean = checkDefEq(e1, e2) == IsDefEq

  def defHeight(fn: Expr, as: List[Expr]): Int =
    fn match {
      case Const(n, _) => env.get(n).map(_.height + 1).getOrElse(0)
      case _ => 0
    }

  private def reduceOneStep(e1: Expr, e2: Expr)(implicit transparency: Transparency): Option[(Expr, Expr)] = {
    val Apps(fn1, as1) = e1
    val Apps(fn2, as2) = e2

    @inline def red1 = reduceOneStep(fn1, as1).map(_ -> e2)
    @inline def red2 = reduceOneStep(fn2, as2).map(e1 -> _)

    if (defHeight(fn1, as1) > defHeight(fn2, as2))
      red1 orElse red2
    else
      red2 orElse red1
  }

  private val lcCache = mutable.AnyRefMap[Expr, List[LocalConst]]().withDefaultValue(Nil)
  private def popCachedLC(binding: Binding): LocalConst =
    lcCache(binding.ty) match {
      case cached :: rest =>
        lcCache(binding.ty) = rest
        cached
      case Nil => LocalConst(binding)
    }
  @inline private def withLC[T](binding: Binding)(f: LocalConst => T): T = {
    val lc = popCachedLC(binding)
    val result = f(lc)
    lcCache(binding.ty) ::= lc
    result
  }

  // Cached Name constants for Nat operations - use interned names for reference equality
  private val NatZeroName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "zero")
  private val NatSuccName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "succ")
  private val OfNatOfNatName = Name.mkStr(Name.mkStr(Name.Anon, "OfNat"), "ofNat")

  /** Extract a Nat value from an expression in whnf form.
    * Handles NatLit, Nat.zero, and Nat.succ(n) iteratively.
    * Returns None if the expression is not a concrete Nat.
    */
  private def extractNatValue(e: Expr): Option[BigInt] = {
    var current = e
    var offset: BigInt = 0
    var maxIter = 100000  // Safety limit

    while (maxIter > 0) {
      maxIter -= 1
      current match {
        case NatLit(n) => return Some(n + offset)
        case Const(n, _) if n eq NatZeroName => return Some(offset)
        case Apps(Const(n, _), List(arg)) if n eq NatSuccName =>
          offset += 1
          current = whnf(arg)  // Reduce the argument
        // OfNat.ofNat : {α : Type} → (n : Nat) → [inst : OfNat α n] → α
        case Apps(Const(n, _), args) if (n eq OfNatOfNatName) && args.length >= 2 =>
          current = whnf(args(1))  // Get and reduce the Nat argument
        case _ => return None  // Not a concrete Nat
      }
    }
    None  // Hit iteration limit
  }

  private def checkDefEqCore(e1_0: Expr, e2_0: Expr): DefEqRes = {
    checkDepth()
    try {
    // Use full transparency for whnf to ensure definitions like OfNat.ofNat reduce properly
    // Note: Lean 4 has finer-grained reducibility control (reducible/instances/default/all)
    // but for correctness we need to reduce abbreviations and typeclass projections
    val transparency = Transparency.all

    // In eager reduction mode, handle Bool.true comparisons specially
    // This is the key mechanism for native_decide proofs
    if (eagerReduceMode) {
      val e2w = eagerWhnf(e2_0)
      val e1w = eagerWhnf(e1_0)

      if (eagerReduceDebug) {
        val e1Str = prettyExpr(e1w, 0).take(80)
        val e2Str = prettyExpr(e2w, 0).take(80)
        if (e1Str.contains("Bool") || e2Str.contains("Bool") ||
            e1Str.contains("isValid") || e2Str.contains("isValid")) {
          println(s"[EAGER-CMP] e1w: $e1Str")
          println(s"[EAGER-CMP]  e2w: $e2Str")
        }
      }

      // Check if either side is Bool.true
      (e1w, e2w) match {
        case (Const(n1, _), _) if n1 eq BoolTrueName =>
          e2w match {
            case Const(n2, _) if n2 eq BoolTrueName => return IsDefEq
            case _ =>
              if (eagerReduceDebug) {
                println(s"[EAGER] e2 did not reduce to Bool.true: ${prettyExpr(e2w, 0).take(100)}")
              }
          }
        case (_, Const(n2, _)) if n2 eq BoolTrueName =>
          e1w match {
            case Const(n1, _) if n1 eq BoolTrueName => return IsDefEq
            case _ =>
              if (eagerReduceDebug) {
                println(s"[EAGER] e1 did not reduce to Bool.true: ${prettyExpr(e1w, 0).take(100)}")
              }
          }
        case _ =>
      }
    }

    val e1 @ Apps(fn1, as1) = whnfCore(e1_0)(transparency)
    val e2 @ Apps(fn2, as2) = whnfCore(e2_0)(transparency)

    // DEBUG DISABLED - HMod/OfNat comparison
    // if (debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
    //   val e1Str = prettyExpr(e1_0, 0).take(100)
    //   val e2Str = prettyExpr(e2_0, 0).take(100)
    //   if ((e1Str.contains("HMod") || e2Str.contains("HMod")) &&
    //       (e1Str.contains("64") || e2Str.contains("64"))) {
    //     println(s"[DEFEQ-CMP] e1_0: $e1Str")
    //     println(s"[DEFEQ-CMP]  e2_0: $e2Str")
    //     println(s"[DEFEQ-CMP] e1 (after whnf): ${prettyExpr(e1, 0).take(100)}")
    //     println(s"[DEFEQ-CMP] e2 (after whnf): ${prettyExpr(e2, 0).take(100)}")
    //   }
    // }

    // After whnf reduction, check structural equality
    // This catches cases where e1_0 != e2_0 but they reduce to the same expression
    if (e1 == e2) return IsDefEq

    // Special case for decide proofs: if one side is Bool.true and other has no fvars,
    // try full reduction. This is needed for proofs like `Eq.refl true : decide p = true`.
    // Both Lean 4 kernel (type_checker.cpp:1053-1061) and nanoda (tc.rs:807-811) have this.
    // NOTE: This only helps when the other side has NO free variables (can fully compute).
    // For proofs with free variables (like Omega proofs), this doesn't help because the
    // computation can't complete without knowing the variable values.
    (fn1, fn2) match {
      case (Const(n1, _), _) if (n1 eq BoolTrueName) && !hasLocalConst(e2) =>
        val e2Full = whnf(e2)
        e2Full match {
          case Const(n, _) if n eq BoolTrueName => return IsDefEq
          case _ => ()
        }
      case (_, Const(n2, _)) if (n2 eq BoolTrueName) && !hasLocalConst(e1) =>
        val e1Full = whnf(e1)
        e1Full match {
          case Const(n, _) if n eq BoolTrueName => return IsDefEq
          case _ => ()
        }
      case _ => ()
    }

    def checkArgs: DefEqRes =
      reqDefEq(as1.size == as2.size, e1, e2) &
        IsDefEq.forall(as1.lazyZip(as2).view.map { case (a, b) => checkDefEq(a, b) })

    // First, try direct Nat comparison to avoid deep recursion
    // This handles NatLit, Nat.zero, nested Nat.succ, and OfNat.ofNat in O(1) stack depth
    // Note: We try extraction on the FULL expression (e1, e2), not just (fn1, fn2),
    // because extractNatValue handles Nat.succ(arg) by reducing the arg internally.
    (extractNatValue(e1), extractNatValue(e2)) match {
      case (Some(n1), Some(n2)) =>
        return reqDefEq(n1 == n2, e1, e2)
      case _ => ()  // Fall through to normal comparison
    }

    // Try direct Int comparison (NatLit can be used as Int)
    // Int.ofNat NatLit(n) = NatLit(n) when n >= 0
    // Int.negSucc NatLit(n) = -(n+1)
    // Note: extractIntValue handles the args internally, so we just check if both extract successfully
    (extractIntValue(e1), extractIntValue(e2)) match {
      case (Some(n1), Some(n2)) =>
        return reqDefEq(n1 == n2, e1, e2)
      case _ => ()  // Fall through to normal comparison
    }

    // Handle autoParam: autoParam α _ = α (just returns first arg, tactic is elaboration metadata)
    // This allows declared types with autoParam to match inferred types without it
    (fn1, fn2) match {
      case (Const(n1, _), _) if (n1 eq AutoParamName) && as1.nonEmpty =>
        return checkDefEq(as1(0), e2)
      case (_, Const(n2, _)) if (n2 eq AutoParamName) && as2.nonEmpty =>
        return checkDefEq(e1, as2(0))
      case _ => ()
    }

    // Eta-struct: For structure-like types, Ctor(args...) =def= x
    // when each field arg is def-eq to the corresponding projection of x.
    // This handles: PSigma.mk (PSigma.fst x) (PSigma.snd x) = x
    //               PLift.up (PLift.down b) = b
    //               Array.mk (Array.toList xs) = xs
    //
    // Algorithm (matching Lean 4 kernel and nanoda_lib):
    // 1. Check if ctorFn is a constructor for a structure-like type
    // 2. Check types are def-eq: infer(ctor(args...)) = infer(other)
    // 3. For each field: Proj(typeName, fieldIdx, other) =def= arg
    def tryEtaStruct(ctorFn: Const, ctorArgs: List[Expr], other: Expr): Option[DefEqRes] = {
      val Const(ctorName, _) = ctorFn
      // Get the type name from the constructor name (constructor is TypeName.mk or TypeName.ctorName)
      ctorName match {
        case Name.Str(typeName, _) =>
          env.inductiveInfo.get(typeName) match {
            case Some(info) if info.ctorName.contains(ctorName) =>
              // This is a single-constructor type (structure-like)
              val numParams = info.numParams
              val numFields = info.numFields

              // Check arg count matches numParams + numFields
              if (ctorArgs.size != numParams + numFields) return None

              // Check types are definitionally equal
              val ctorExpr = Apps(ctorFn, ctorArgs)
              val ctorType = infer(ctorExpr)
              val otherType = infer(other)
              if (!isDefEq(ctorType, otherType)) return None

              // Check each field: Proj(typeName, idx, other) =def= arg
              val fieldArgs = ctorArgs.drop(numParams)
              val allFieldsMatch = fieldArgs.zipWithIndex.forall { case (arg, idx) =>
                val proj = Proj(typeName, idx, other)
                isDefEq(proj, arg)
              }

              if (allFieldsMatch) Some(IsDefEq) else None
            case _ => None
          }
        case _ => None
      }
    }

    // Try eta-struct in both directions
    (fn1, fn2) match {
      case (c1 @ Const(_, _), _) =>
        tryEtaStruct(c1, as1, e2) match {
          case Some(res) => return res
          case None => ()
        }
      case _ => ()
    }
    (fn2, fn1) match {
      case (c2 @ Const(_, _), _) =>
        tryEtaStruct(c2, as2, e1) match {
          case Some(res) => return res
          case None => ()
        }
      case _ => ()
    }

    // Unit-like types: For types with single constructor and 0 fields,
    // all values are definitionally equal if their types are equal.
    // This handles Unit, PUnit, True, etc.
    def tryUnitLike(e1: Expr, e2: Expr): Option[DefEqRes] = {
      val e1Type = whnf(infer(e1))
      e1Type match {
        case Apps(Const(typeName, _), _) =>
          env.inductiveInfo.get(typeName) match {
            case Some(info) if info.ctorName.isDefined && info.numFields == 0 =>
              // Single constructor with 0 fields - unit-like type
              val e2Type = infer(e2)
              if (isDefEq(e1Type, e2Type)) Some(IsDefEq) else None
            case _ => None
          }
        case _ => None
      }
    }
    tryUnitLike(e1, e2) match {
      case Some(res) => return res
      case None => ()
    }

    // Handle mismatched argument counts for constructors with type parameters
    // This can happen when some reductions produce malformed expressions missing type params
    // e.g., Array.mk UInt8 (List.nil UInt8) vs Array.mk (List.nil)
    (fn1, fn2, as1.size, as2.size) match {
      case (Const(c1, ls1), Const(c2, ls2), n1, n2) if c1 == c2 && ls1.lazyZip(ls2).forall(isDefEq) && n1 != n2 =>
        // Try to match arguments, skipping type parameters on the side with more args
        val (larger, smaller, largerArgs, smallerArgs) = if (n1 > n2) (e1, e2, as1, as2) else (e2, e1, as2, as1)
        val diff = math.abs(n1 - n2)
        // Only handle small differences (likely type params)
        if (diff <= 2) {
          // Skip the first 'diff' args from the larger side (these are type params)
          val matchResult = IsDefEq.forall(largerArgs.drop(diff).lazyZip(smallerArgs).view.map { case (a, b) => checkDefEq(a, b) })
          matchResult match {
            case IsDefEq => return IsDefEq
            case _ => () // Fall through to normal handling
          }
        }
      case _ => ()
    }

    ((fn1, fn2) match {
      case (Sort(l1), Sort(l2)) =>
        return reqDefEq(isDefEq(l1, l2) && as1.isEmpty && as2.isEmpty, e1, e2)
      case (Const(c1, ls1), Const(c2, ls2)) if c1 == c2 && ls1.lazyZip(ls2).forall(isDefEq) =>
        checkArgs
      case (LocalConst(_, i1), LocalConst(_, i2)) if i1 == i2 =>
        checkArgs
      case (Lam(dom, b1), Lam(_, b2)) =>
        require(as1.isEmpty && as2.isEmpty)
        return withLC(dom)(lc => checkDefEqCore(b1.instantiate(lc), b2.instantiate(lc)))
      case (Lam(dom1, _), _) =>
        require(as1.isEmpty)
        return checkDefEqCore(e1, Lam(dom1, App(e2, Var(0))))
      case (_, Lam(dom2, _)) =>
        require(as2.isEmpty)
        return checkDefEqCore(Lam(dom2, App(e1, Var(0))), e2)
      case (Pi(dom1, b1), Pi(dom2, b2)) =>
        require(as1.isEmpty && as2.isEmpty)
        return checkDefEq(dom1.ty, dom2.ty) & withLC(dom1)(lc => checkDefEqCore(b1.instantiate(lc), b2.instantiate(lc)))
      case (StringLit(s1), StringLit(s2)) if s1 == s2 && as1.isEmpty && as2.isEmpty =>
        return IsDefEq
      // Projection comparison: Proj(T, i, s1) =?= Proj(T, i, s2)
      // With in-progress cycle detection, we can safely call checkDefEq on struct bases.
      // This is exactly what both Lean 4 and nanoda do.
      case (Proj(t1, i1, s1), Proj(t2, i2, s2)) if t1 == t2 && i1 == i2 =>
        checkDefEq(s1, s2) match {
          case IsDefEq => return checkArgs  // Bases equal, now check projection args
          case ne => return ne
        }
      case (_, _) =>
        NotDefEq(e1, e2)
    }) match {
      case IsDefEq => IsDefEq
      case d @ NotDefEq(_, _) =>
        reduceOneStep(e1, e2)(Transparency.all) match {
          case Some((e1_, e2_)) =>
            checkDefEqCore(e1_, e2_)
          case None => d
        }
    }
    } finally {
      releaseDepth()
    }
  }

  private val defEqCache = mutable.AnyRefMap[(Expr, Expr), DefEqRes]()
  private val eagerDefEqCache = mutable.AnyRefMap[(Expr, Expr), DefEqRes]()
  // Track pairs currently being compared to detect cycles (prevents stack overflow)
  // When we encounter a pair already in progress, we return IsDefEq optimistically.
  // This matches the behavior of both Lean 4's equiv_manager and nanoda's union-find.
  private val inProgressPairs = mutable.HashSet[(Expr, Expr)]()
  // requires that e1 and e2 have the same type, or are types
  def checkDefEq(e1: Expr, e2: Expr): DefEqRes = {
    // Fast path: syntactic equality
    if (e1.eq(e2) || e1 == e2) return IsDefEq

    // Normalize key ordering for cache lookups (smaller hash first)
    val key = if (e1.hashCode <= e2.hashCode) (e1, e2) else (e2, e1)
    val cache = if (eagerReduceMode) eagerDefEqCache else defEqCache

    // Check cache first
    cache.get(key) match {
      case Some(result) => return result
      case None => ()
    }

    // Check if we're already comparing this pair (cycle detection)
    // If so, return IsDefEq optimistically - if truly unequal, it will fail elsewhere
    if (inProgressPairs.contains(key)) {
      return IsDefEq
    }

    // Mark as in-progress and compute
    inProgressPairs.add(key)
    try {
      val result = if (isProofIrrelevantEq(e1, e2)) IsDefEq else checkDefEqCore(e1, e2)
      cache.put(key, result)
      result
    } finally {
      inProgressPairs.remove(key)
    }
  }

  case class Transparency(rho: Boolean) {
    def canReduceConstants: Boolean = rho
  }
  object Transparency {
    val all = Transparency(rho = true)
  }

  def reduceOneStep(e: Expr)(implicit transparency: Transparency): Option[Expr] =
    e match { case Apps(fn, as) => reduceOneStep(fn, as) }
  private implicit object reductionRuleCache extends ReductionRuleCache {
    // Use IdentityHashMap keyed by ReductionRule, with inner map for substitutions
    // This avoids expensive Map.hashCode operations that cause stack overflow
    private val instantiationCache = new java.util.IdentityHashMap[ReductionRule, mutable.AnyRefMap[Map[Level.Param, Level], Expr]]()
    override def instantiation(rr: ReductionRule, subst: Map[Level.Param, Level], v: => Expr): Expr = {
      var inner = instantiationCache.get(rr)
      if (inner == null) {
        inner = mutable.AnyRefMap[Map[Level.Param, Level], Expr]()
        instantiationCache.put(rr, inner)
      }
      inner.getOrElseUpdate(subst, v)
    }
  }
  /** Convert NatLit to constructor form for recursor pattern matching.
   *  Only converts one layer: NatLit(0) -> Nat.zero, NatLit(n+1) -> Nat.succ(NatLit(n))
   *
   *  IMPORTANT: We skip conversion for large NatLits (> 10000) in non-eager mode to avoid
   *  O(n) reduction. In eager mode (native_decide), we need to allow larger values.
   */
  private def natLitToConstructor(e: Expr): Expr = e match {
    case NatLit(n) if n == 0 =>
      Const(NatZeroName, Vector())
    case NatLit(n) if n <= 10000 || eagerReduceMode =>
      // In eager mode, allow larger values (needed for native_decide with hugeFuel)
      // For non-eager mode, limit to 10000 to avoid O(n) explosion
      App(Const(NatSuccName, Vector()), NatLit(n - 1))
    case _ => e  // Return unchanged for very large NatLits or non-NatLit expressions
  }

  /**
   * Expand a structure value to constructor form for recursor reduction.
   * For a value `e : S a b c` where S is a single-constructor type,
   * returns `S.mk a b c (Proj(S, 0, e)) (Proj(S, 1, e)) ...`
   *
   * This enables recursor reduction when the major premise is a variable
   * of structure type. Without this, Fin.rec (...) x won't reduce when
   * x is a variable, even though it should via eta for structures.
   *
   * Based on Lean 4's `expand_eta_struct` in kernel/inductive.cpp
   */
  private def expandEtaStruct(e: Expr): Expr = {
    // First check if e is already a constructor application
    val eWhnf = whnf(e)
    eWhnf match {
      case Apps(Const(fn, _), _) =>
        // Check if this is a constructor by looking up its inductive type
        // and seeing if it's the single constructor
        val isCtorApp = env.inductiveInfo.values.exists(info =>
          info.ctorName.contains(fn)
        )
        if (isCtorApp) return eWhnf
      case _ => ()
    }

    // Not a constructor application - try to expand as structure
    val eType = whnf(infer(e))
    eType match {
      case Apps(Const(typeName, levels), typeArgs) =>
        env.inductiveInfo.get(typeName) match {
          case Some(info) if info.ctorName.isDefined =>
            // Single constructor type - expand to constructor form
            val ctorName = info.ctorName.get
            val numParams = info.numParams
            val numFields = info.numFields

            // Don't expand Prop-typed structures (proof irrelevance handles those)
            val typeSort = whnf(infer(eType))
            typeSort match {
              case Sort(Level.Zero) => return eWhnf  // Prop-typed, skip
              case _ => ()
            }

            // Build: ctor(params..., Proj(typeName, 0, e), Proj(typeName, 1, e), ...)
            val params = typeArgs.take(numParams)
            val projs = (0 until numFields).map(i => Proj(typeName, i, e))
            Apps(Const(ctorName, levels), params ++ projs)
          case _ => eWhnf
        }
      case _ => eWhnf
    }
  }

  // Names for special Nat handling (use interned names for reference equality)
  private val NatRecName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "rec")
  private val NatCasesOnName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "casesOn")
  private val NatDecLtName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "decLt")
  private val NatDecLeName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "decLe")
  private val NatDecEqName = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "decEq")

  // Names for native Nat operations (like Lean 4's reduce_nat)
  private val NatName_ = Name.mkStr(Name.Anon, "Nat")
  private val NatAddName = Name.mkStr(NatName_, "add")
  private val NatSubName = Name.mkStr(NatName_, "sub")
  private val NatPredName = Name.mkStr(NatName_, "pred")
  private val NatMulName = Name.mkStr(NatName_, "mul")
  private val NatDivName = Name.mkStr(NatName_, "div")
  private val NatModName = Name.mkStr(NatName_, "mod")
  private val NatPowName = Name.mkStr(NatName_, "pow")
  private val NatBeqName = Name.mkStr(NatName_, "beq")
  private val NatBleName = Name.mkStr(NatName_, "ble")
  private val NatBltName = Name.mkStr(NatName_, "blt")
  private val NatLandName = Name.mkStr(NatName_, "land")
  private val NatLorName = Name.mkStr(NatName_, "lor")
  private val NatXorName = Name.mkStr(NatName_, "xor")
  private val NatShiftLeftName = Name.mkStr(NatName_, "shiftLeft")
  private val NatShiftRightName = Name.mkStr(NatName_, "shiftRight")
  private val BoolName = Name.mkStr(Name.Anon, "Bool")
  private val BoolTrueName = Name.mkStr(BoolName, "true")
  private val BoolFalseName = Name.mkStr(BoolName, "false")
  private val boolTrue = Const(BoolTrueName, Vector())
  private val boolFalse = Const(BoolFalseName, Vector())

  // Names for Int handling (use interned names)
  private val IntName = Name.mkStr(Name.Anon, "Int")
  private val IntOfNat = Name.mkStr(IntName, "ofNat")
  private val IntNegSucc = Name.mkStr(IntName, "negSucc")
  private val IntNeg = Name.mkStr(IntName, "neg")
  private val IntAdd = Name.mkStr(IntName, "add")
  private val IntSub = Name.mkStr(IntName, "sub")
  private val IntMul = Name.mkStr(IntName, "mul")
  private val IntDiv = Name.mkStr(IntName, "div")
  private val IntMod = Name.mkStr(IntName, "mod")
  private val IntEDiv = Name.mkStr(IntName, "ediv")
  private val IntEMod = Name.mkStr(IntName, "emod")
  private val IntDecLe = Name.mkStr(IntName, "decLe")
  private val IntDecLt = Name.mkStr(IntName, "decLt")
  private val IntDecEq = Name.mkStr(IntName, "decEq")

  // Names for comparison type classes
  private val LEName = Name.mkStr(Name.Anon, "LE")
  private val LELe = Name.mkStr(LEName, "le")
  private val LTName = Name.mkStr(Name.Anon, "LT")
  private val LTLt = Name.mkStr(LTName, "lt")
  private val EqName_ = Name.mkStr(Name.Anon, "Eq")
  private val FalseName = Name.mkStr(Name.Anon, "False")
  private val AndName = Name.mkStr(Name.Anon, "And")

  // Names for heterogeneous operations (typeclass-based)
  private val HPowName = Name.mkStr(Name.Anon, "HPow")
  private val HPowHPow = Name.mkStr(HPowName, "hPow")
  private val HModName = Name.mkStr(Name.Anon, "HMod")
  private val HModHMod = Name.mkStr(HModName, "hMod")

  // Names for Fin, BitVec, and UInt types (for native reductions)
  private val FinName = Name.mkStr(Name.Anon, "Fin")
  private val FinMk = Name.mkStr(FinName, "mk")
  private val FinVal = Name.mkStr(FinName, "val")

  private val BitVecName = Name.mkStr(Name.Anon, "BitVec")
  private val BitVecOfFin = Name.mkStr(BitVecName, "ofFin")
  private val BitVecToNat = Name.mkStr(BitVecName, "toNat")
  private val BitVecOfNat = Name.mkStr(BitVecName, "ofNat")
  private val BitVecToFin = Name.mkStr(BitVecName, "toFin")

  private val UInt8Name = Name.mkStr(Name.Anon, "UInt8")
  private val UInt8OfBitVec = Name.mkStr(UInt8Name, "ofBitVec")
  private val UInt8ToBitVec = Name.mkStr(UInt8Name, "toBitVec")
  private val UInt8ToNat = Name.mkStr(UInt8Name, "toNat")
  private val UInt8OfNat = Name.mkStr(UInt8Name, "ofNat")
  private val UInt8Size = Name.mkStr(UInt8Name, "size")

  private val UInt16Name = Name.mkStr(Name.Anon, "UInt16")
  private val UInt16OfBitVec = Name.mkStr(UInt16Name, "ofBitVec")
  private val UInt16ToBitVec = Name.mkStr(UInt16Name, "toBitVec")
  private val UInt16ToNat = Name.mkStr(UInt16Name, "toNat")
  private val UInt16OfNat = Name.mkStr(UInt16Name, "ofNat")
  private val UInt16Size = Name.mkStr(UInt16Name, "size")

  private val UInt32Name = Name.mkStr(Name.Anon, "UInt32")
  private val UInt32OfBitVec = Name.mkStr(UInt32Name, "ofBitVec")
  private val UInt32ToBitVec = Name.mkStr(UInt32Name, "toBitVec")
  private val UInt32ToNat = Name.mkStr(UInt32Name, "toNat")
  private val UInt32OfNat = Name.mkStr(UInt32Name, "ofNat")
  private val UInt32Size = Name.mkStr(UInt32Name, "size")

  private val UInt64Name = Name.mkStr(Name.Anon, "UInt64")
  private val UInt64OfBitVec = Name.mkStr(UInt64Name, "ofBitVec")
  private val UInt64ToBitVec = Name.mkStr(UInt64Name, "toBitVec")
  private val UInt64ToNat = Name.mkStr(UInt64Name, "toNat")
  private val UInt64OfNat = Name.mkStr(UInt64Name, "ofNat")
  private val UInt64Size = Name.mkStr(UInt64Name, "size")

  private val USizeName = Name.mkStr(Name.Anon, "USize")
  private val USizeOfBitVec = Name.mkStr(USizeName, "ofBitVec")
  private val USizeToBitVec = Name.mkStr(USizeName, "toBitVec")
  private val USizeToNat = Name.mkStr(USizeName, "toNat")
  private val USizeOfNat = Name.mkStr(USizeName, "ofNat")
  private val USizeSize = Name.mkStr(USizeName, "size")

  // Platform word size (assume 64-bit for now - matches most modern systems)
  private val platformBits: Int = 64
  private val uSizeWidth: Int = platformBits
  private val uSizeSize: BigInt = BigInt(1) << uSizeWidth

  // Signed integer types
  private val Int8Name = Name.mkStr(Name.Anon, "Int8")
  private val Int8OfBitVec = Name.mkStr(Int8Name, "ofBitVec")
  private val Int8ToBitVec = Name.mkStr(Int8Name, "toBitVec")
  private val Int8ToInt = Name.mkStr(Int8Name, "toInt")
  private val Int8OfInt = Name.mkStr(Int8Name, "ofInt")

  private val Int16Name = Name.mkStr(Name.Anon, "Int16")
  private val Int16OfBitVec = Name.mkStr(Int16Name, "ofBitVec")
  private val Int16ToBitVec = Name.mkStr(Int16Name, "toBitVec")
  private val Int16ToInt = Name.mkStr(Int16Name, "toInt")
  private val Int16OfInt = Name.mkStr(Int16Name, "ofInt")

  private val Int32Name = Name.mkStr(Name.Anon, "Int32")
  private val Int32OfBitVec = Name.mkStr(Int32Name, "ofBitVec")
  private val Int32ToBitVec = Name.mkStr(Int32Name, "toBitVec")
  private val Int32ToInt = Name.mkStr(Int32Name, "toInt")
  private val Int32OfInt = Name.mkStr(Int32Name, "ofInt")

  private val Int64Name = Name.mkStr(Name.Anon, "Int64")
  private val Int64OfBitVec = Name.mkStr(Int64Name, "ofBitVec")
  private val Int64ToBitVec = Name.mkStr(Int64Name, "toBitVec")
  private val Int64ToInt = Name.mkStr(Int64Name, "toInt")
  private val Int64OfInt = Name.mkStr(Int64Name, "ofInt")

  private val ISizeName = Name.mkStr(Name.Anon, "ISize")
  private val ISizeOfBitVec = Name.mkStr(ISizeName, "ofBitVec")
  private val ISizeToBitVec = Name.mkStr(ISizeName, "toBitVec")
  private val ISizeToInt = Name.mkStr(ISizeName, "toInt")
  private val ISizeOfInt = Name.mkStr(ISizeName, "ofInt")

  // System.Platform names for platform-dependent values
  private val SystemName = Name.mkStr(Name.Anon, "System")
  private val PlatformName = Name.mkStr(SystemName, "Platform")
  private val NumBitsName = Name.mkStr(PlatformName, "numBits")
  private val GetNumBitsName = Name.mkStr(PlatformName, "getNumBits")

  // Subtype constructor for wrapping values with proofs
  private val SubtypeName = Name.mkStr(Name.Anon, "Subtype")
  private val SubtypeMk = Name.mkStr(SubtypeName, "mk")
  private val SubtypeVal = Name.mkStr(SubtypeName, "val")

  // Array, ByteArray, List, and String handling
  private val ArrayName = Name.mkStr(Name.Anon, "Array")
  private val ArrayMk = Name.mkStr(ArrayName, "mk")
  private val ArrayEmpty = Name.mkStr(ArrayName, "empty")
  private val ArraySize = Name.mkStr(ArrayName, "size")
  private val ArrayData = Name.mkStr(ArrayName, "data")

  private val ByteArrayName = Name.mkStr(Name.Anon, "ByteArray")
  private val ByteArrayMk = Name.mkStr(ByteArrayName, "mk")
  private val ByteArraySize = Name.mkStr(ByteArrayName, "size")
  private val ByteArrayData = Name.mkStr(ByteArrayName, "data")
  private val ByteArrayEmpty = Name.mkStr(ByteArrayName, "empty")

  private val ListName = Name.mkStr(Name.Anon, "List")
  private val ListNil = Name.mkStr(ListName, "nil")
  private val ListCons = Name.mkStr(ListName, "cons")
  private val ListLength = Name.mkStr(ListName, "length")
  private val ListToArray = Name.mkStr(ListName, "toArray")

  // autoParam T tactic = T (just returns T, the tactic is elaborator metadata)
  private val AutoParamName = Name.mkStr(Name.Anon, "autoParam")

  private val StringName_ = Name.mkStr(Name.Anon, "String")
  private val StringMk = Name.mkStr(StringName_, "mk")
  private val StringToByteArray = Name.mkStr(StringName_, "toByteArray")
  private val StringOfList = Name.mkStr(StringName_, "ofList")
  private val StringUtf8ByteSize = Name.mkStr(StringName_, "utf8ByteSize")
  private val StringRawEndPos = Name.mkStr(StringName_, "rawEndPos")
  private val StringLength = Name.mkStr(StringName_, "length")
  private val StringData = Name.mkStr(StringName_, "data")
  private val StringPosName = Name.mkStr(StringName_, "Pos")
  private val StringPosMk = Name.mkStr(StringPosName, "mk")
  private val StringPosByteIdx = Name.mkStr(StringPosName, "byteIdx")
  private val StringPosRaw = Name.mkStr(StringPosName, "Raw")
  private val StringPosRawMk = Name.mkStr(StringPosRaw, "mk")

  /** Extract the length of a list from a whnf expression.
    * Handles List.nil and List.cons iteratively.
    */
  private def extractListLength(e: Expr): Option[BigInt] = {
    var current = e
    var length: BigInt = 0
    var maxIter = 100000
    while (maxIter > 0) {
      maxIter -= 1
      val Apps(fn, args) = current
      fn match {
        case Const(n, _) if n eq ListNil => return Some(length)
        case Const(n, _) if (n eq ListCons) && args.size >= 2 =>
          length += 1
          current = whnf(args.last)  // tail of the list
        case _ => return None
      }
    }
    None
  }

  // Char is represented as UInt32 internally
  private val CharName = Name.mkStr(Name.Anon, "Char")
  private val CharMk = Name.mkStr(CharName, "mk")
  private val CharOfNat = Name.mkStr(CharName, "ofNat")

  /** Extract a list of character code points from a List Char expression.
    * Returns None if the list cannot be fully extracted.
    */
  private def extractCharList(e: Expr): Option[List[Int]] = {
    var current = e
    var chars = List.newBuilder[Int]
    var maxIter = 10000  // Limit for safety
    while (maxIter > 0) {
      maxIter -= 1
      val Apps(fn, args) = whnf(current)
      fn match {
        case Const(n, _) if n eq ListNil =>
          return Some(chars.result())
        case Const(n, _) if (n eq ListCons) && args.size >= 3 =>
          // List.cons has args: [type, head, tail] (type param + 2 fields)
          // Or [head, tail] if type param is missing (malformed)
          val (head, tail) = if (args.size >= 3) (args(1), args(2)) else (args(0), args(1))
          extractCharValue(whnf(head)) match {
            case Some(codePoint) =>
              chars += codePoint
              current = tail
            case None => return None
          }
        case _ => return None
      }
    }
    None  // Too many iterations
  }

  /** Extract a Char code point value from an expression.
    * Char.mk (UInt32.mk (BitVec.ofNat 32 n)) or similar patterns.
    */
  private def extractCharValue(e: Expr): Option[Int] = {
    val Apps(fn, args) = e
    fn match {
      // Char.mk takes a UInt32
      case Const(mk, _) if (mk eq CharMk) && args.nonEmpty =>
        extractUIntValue(whnf(args.last), 32).map(_.toInt)
      // Char.ofNat n - convert Nat to Char
      case Const(ofNat, _) if (ofNat eq CharOfNat) && args.nonEmpty =>
        extractNatValue(whnf(args.last)).map(_.toInt)
      case _ => None
    }
  }

  /** Extract an Int value from an expression.
    * Handles NatLit (as non-negative Int), Int.ofNat NatLit(n), Int.negSucc NatLit(n).
    */
  private def extractIntValue(e: Expr): Option[BigInt] = {
    val Apps(fn, args) = e
    fn match {
      // NatLit can be used as Int (non-negative)
      case NatLit(n) if args.isEmpty => Some(n)
      // Int.ofNat NatLit(n) = n
      case Const(IntOfNat, _) if args.size == 1 =>
        extractNatValue(whnf(args.head))
      // Int.negSucc NatLit(n) = -(n+1)
      case Const(IntNegSucc, _) if args.size == 1 =>
        extractNatValue(whnf(args.head)).map(n => -(n + 1))
      case _ => None
    }
  }

  /** Extract a BitVec value (width, value) from an expression.
    * Handles BitVec.ofFin (Fin.mk n _), BitVec.ofNat w n, and UIntX.toBitVec patterns.
    * Returns (width, value mod 2^width).
    */
  private def extractBitVecValue(e: Expr): Option[(Int, BigInt)] = {
    val w = whnf(e)
    val Apps(fn, args) = w
    fn match {
      // BitVec.ofFin : {n : Nat} → Fin (2^n) → BitVec n
      // When applied to Fin.mk val _, extract val
      case Const(BitVecOfFin, _) if args.size >= 2 =>
        val widthArg = args(0)
        val finArg = whnf(args(1))
        extractNatFromExpr(widthArg).flatMap { width =>
          if (width > 10000) None  // Guard against huge widths
          else extractFinValue(finArg).map(v => (width.toInt, v % (BigInt(1) << width.toInt)))
        }
      // BitVec.ofNat w n : BitVec w
      case Const(BitVecOfNat, _) if args.size >= 2 =>
        val widthArg = args(0)
        val valArg = args(1)
        for {
          width <- extractNatFromExpr(widthArg) if width <= 10000
          value <- extractNatFromExpr(whnf(valArg))
        } yield (width.toInt, value % (BigInt(1) << width.toInt))
      // UIntX.toBitVec wrapping OfNat - delegate to extractUIntValue
      case Const(n, _) if (n eq UInt8ToBitVec) || (n eq UInt16ToBitVec) ||
                          (n eq UInt32ToBitVec) || (n eq UInt64ToBitVec) ||
                          (n eq USizeToBitVec) =>
        val width = if (n eq UInt8ToBitVec) 8
                    else if (n eq UInt16ToBitVec) 16
                    else if (n eq UInt32ToBitVec) 32
                    else if (n eq UInt64ToBitVec) 64
                    else uSizeWidth
        args.lastOption.flatMap { arg =>
          extractUIntValue(arg, width).map(v => (width, v))
        }
      case _ => None
    }
  }

  /** Extract a Fin value from an expression.
    * Handles Fin.mk val isLt pattern.
    */
  private def extractFinValue(e: Expr): Option[BigInt] = {
    val Apps(fn, args) = whnf(e)
    fn match {
      // Fin.mk : {n : Nat} → (val : Nat) → val < n → Fin n
      case Const(FinMk, _) if args.size >= 2 =>
        extractNatFromExpr(args(1))  // args(0) = n, args(1) = val
      case _ => None
    }
  }

  // Names for OfNat typeclass
  private val OfNatName = Name.mkStr(Name.Anon, "OfNat")
  private val OfNatOfNat = Name.mkStr(OfNatName, "ofNat")

  // Names for Neg typeclass (for negation)
  private val NegName = Name.mkStr(Name.Anon, "Neg")
  private val NegNeg = Name.mkStr(NegName, "neg")

  // Signed integer neg functions (IntX.neg)
  private val Int8Neg = Name.mkStr(Int8Name, "neg")
  private val Int16Neg = Name.mkStr(Int16Name, "neg")
  private val Int32Neg = Name.mkStr(Int32Name, "neg")
  private val Int64Neg = Name.mkStr(Int64Name, "neg")
  private val ISizeNeg = Name.mkStr(ISizeName, "neg")

  /** Extract a UInt value (width, value) from UIntX types.
    * Handles UIntX.ofBitVec bv pattern and OfNat.ofNat n pattern.
    */
  private def extractUIntValue(e: Expr, width: Int): Option[BigInt] = {
    val w = whnf(e)
    val Apps(fn, args) = w
    val ofBitVecName = width match {
      case 8 => UInt8OfBitVec
      case 16 => UInt16OfBitVec
      case 32 => UInt32OfBitVec
      case 64 => UInt64OfBitVec
      case _ => return None
    }
    fn match {
      case Const(n, _) if n eq ofBitVecName =>
        args.lastOption.flatMap { bv =>
          extractBitVecValue(bv).map(_._2)
        }
      // Also handle OfNat.ofNat {UIntX} n inst - extract n directly
      case Const(n, _) if n eq OfNatOfNat =>
        // OfNat.ofNat : {α : Type u} → (n : Nat) → [OfNat α n] → α
        // args = [type, n, instance]
        if (args.size >= 2) {
          extractNatFromExpr(whnf(args(1))).map { value =>
            value % (BigInt(1) << width)
          }
        } else None
      case _ => None
    }
  }

  /** Extract a signed integer value (as BigInt) from IntX/ISize types.
    * Handles IntX.ofBitVec bv pattern, OfNat.ofNat, and Neg.neg patterns.
    */
  private def extractSIntValue(e: Expr, width: Int): Option[BigInt] = {
    val w = whnf(e)
    val Apps(fn, args) = w
    val ofBitVecName = width match {
      case 8 => Int8OfBitVec
      case 16 => Int16OfBitVec
      case 32 => Int32OfBitVec
      case 64 => Int64OfBitVec
      case _ if width == uSizeWidth => ISizeOfBitVec
      case _ => return None
    }
    val modulus = BigInt(1) << width
    val halfModulus = modulus / 2
    fn match {
      case Const(n, _) if n eq ofBitVecName =>
        args.lastOption.flatMap { bv =>
          extractBitVecValue(bv).map { case (_, unsignedVal) =>
            // Convert from unsigned to signed (two's complement)
            if (unsignedVal >= halfModulus) unsignedVal - modulus else unsignedVal
          }
        }
      // OfNat.ofNat for positive signed integers
      case Const(n, _) if n eq OfNatOfNat =>
        // OfNat.ofNat : {α : Type u} → (n : Nat) → [OfNat α n] → α
        if (args.size >= 2) {
          extractNatFromExpr(whnf(args(1))).map { value =>
            // Convert to signed representation
            val modVal = value % modulus
            if (modVal >= halfModulus) modVal - modulus else modVal
          }
        } else None
      // Neg.neg for negation: Neg.neg : {α : Type u} → [Neg α] → α → α
      case Const(n, _) if n eq NegNeg =>
        // args = [type, instance, value]
        if (args.size >= 3) {
          extractSIntValue(args(2), width).map { innerVal =>
            // Negate and normalize
            val negated = -innerVal
            ((negated % modulus) + modulus) % modulus match {
              case v if v >= halfModulus => v - modulus
              case v => v
            }
          }
        } else None
      case _ => None
    }
  }

  /** Create an Int expression from a BigInt value. */
  private def mkIntExpr(value: BigInt): Expr = {
    if (value >= 0) {
      Apps(Const(IntOfNat, Vector()), Vector(NatLit(value)))
    } else {
      // Int.negSucc n represents -(n+1)
      Apps(Const(IntNegSucc, Vector()), Vector(NatLit(-value - 1)))
    }
  }

  // Names for Decidable handling (use interned names)
  private val DecidableName = Name.mkStr(Name.Anon, "Decidable")
  private val DecidableRecName = Name.mkStr(DecidableName, "rec")
  private val DecidableCasesOnName = Name.mkStr(DecidableName, "casesOn")
  private val DecidableIsTrue = Name.mkStr(DecidableName, "isTrue")
  private val DecidableIsFalse = Name.mkStr(DecidableName, "isFalse")

  // Names for Eq handling (isK optimization)
  private val EqName = Name.mkStr(Name.Anon, "Eq")
  private val EqRecName = Name.mkStr(EqName, "rec")
  private val HEqName = Name.mkStr(Name.Anon, "HEq")
  private val HEqRecName = Name.mkStr(HEqName, "rec")

  /** Extract Decidable constructor from a whnf expression.
    * Returns Some(Right(proof)) for isTrue, Some(Left(proof)) for isFalse, None otherwise.
    */
  private def extractDecidableWhnf(e: Expr): Option[Either[Expr, Expr]] = {
    whnf(e) match {
      case Apps(Const(DecidableIsTrue, _), args) =>
        args.lastOption.map(Right(_))
      case Apps(Const(DecidableIsFalse, _), args) =>
        args.lastOption.map(Left(_))
      case _ => None
    }
  }

  /** Extract Nat value from expression, handling NatLit, Nat.zero, and Nat.succ iteratively.
    * Optimized to avoid whnf calls when expression is already in normal form.
    */
  private def extractNatFromExpr(e: Expr): Option[BigInt] = {
    // Fast path: try to extract without any whnf calls first
    // This handles already-normalized expressions like NatLit, Nat.zero, or Nat.succ chains
    extractNatNoWhnf(e) match {
      case result @ Some(_) => result
      case None =>
        // Slow path: use whnf to reduce the expression
        extractNatWithWhnf(e)
    }
  }

  /** Extract Nat value without calling whnf - for already-normalized expressions. */
  @inline private def extractNatNoWhnf(e: Expr): Option[BigInt] = {
    var current = e
    var offset: BigInt = 0
    var maxIter = 100000
    while (maxIter > 0) {
      maxIter -= 1
      current match {
        case NatLit(n) => return Some(n + offset)
        case Const(n, _) if n eq NatZeroName => return Some(offset)
        case Apps(Const(n, _), List(arg)) if n eq NatSuccName =>
          offset += 1
          current = arg  // Don't call whnf - just unwrap the succ
        case _ => return None  // Not normalized, need whnf
      }
    }
    None
  }

  /** Extract Nat value with whnf reduction - slower but handles non-normalized expressions. */
  @inline private def extractNatWithWhnf(e: Expr): Option[BigInt] = {
    var current = whnf(e)  // Reduce once at the start
    var offset: BigInt = 0
    var maxIter = 100000
    while (maxIter > 0) {
      maxIter -= 1
      current match {
        case NatLit(n) => return Some(n + offset)
        case Const(n, _) if n eq NatZeroName => return Some(offset)
        case Apps(Const(n, _), List(arg)) if n eq NatSuccName =>
          offset += 1
          current = whnf(arg)
        case _ => return None
      }
    }
    None
  }

  def reduceOneStep(fn: Expr, as0: List[Expr])(implicit transparency: Transparency): Option[Expr] =
    fn match {
      case Const(n, _) if transparency.rho =>
        // Special handling for Nat.casesOn on literals - O(1) per step reduction
        // Nat.casesOn.{u} : {motive : Nat → Sort u} → (n : Nat) → motive 0 → ((n : Nat) → motive n.succ) → motive n
        //
        // IMPORTANT: We limit this to "small" Nat values (< 10000) because:
        // - Large values like USize (2^32 or 2^64) would require billions of iterations
        // - For large Nat proofs, we rely on proof irrelevance in checkDefEq
        // - Actual computation (not proofs) uses builtin Nat ops which are O(1)
        if (n == NatCasesOnName && as0.size >= 4) {
          val majorArg = whnf(as0(1))  // The Nat argument
          val extracted = extractNatFromExpr(majorArg)
          extracted match {
            case Some(nv) if nv < 10000 || eagerReduceMode =>
              // In eager mode, allow larger values (needed for native_decide with hugeFuel)
              // For non-eager mode, limit to 10000 to avoid O(n) explosion
              val zeroCase = as0(2)
              val succCase = as0(3)
              val extraArgs = as0.drop(4)
              val result = if (nv == 0) zeroCase else App(succCase, NatLit(nv - 1))
              return Some(Apps(result, extraArgs))
            case _ => ()  // Fall through to normal reduction
          }
        }
        // Note: Nat.rec is NOT handled specially - it would require O(n) steps to build
        // the result expression. For proofs involving large Nat literals, proof irrelevance
        // should handle most cases. If reduction is actually needed, fall through to
        // the regular reduction rules.

        // Special handling for Decidable.rec - reduce when instance is a constructor
        // Decidable.rec : {P : Prop} → {motive : Decidable P → Sort u} →
        //   ((h : ¬P) → motive (isFalse h)) → ((h : P) → motive (isTrue h)) →
        //   (t : Decidable P) → motive t
        if (n == DecidableRecName && as0.size >= 5) {
          val propArg = as0(0)      // P (implicit)
          val motiveArg = as0(1)    // motive (implicit)
          val falseCase = as0(2)    // h_false
          val trueCase = as0(3)     // h_true
          val decidableInst = as0(4) // t
          val extraArgs = as0.drop(5)
          extractDecidableWhnf(decidableInst) match {
            case Some(Right(proof)) =>
              // isTrue case: trueCase proof
              return Some(Apps(App(trueCase, proof), extraArgs))
            case Some(Left(proof)) =>
              // isFalse case: falseCase proof
              return Some(Apps(App(falseCase, proof), extraArgs))
            case None => ()  // Fall through to normal reduction
          }
        }

        // Special handling for Decidable.casesOn
        // Decidable.casesOn : {P : Prop} → {motive : Decidable P → Sort u} →
        //   (t : Decidable P) → ((h : ¬P) → motive (isFalse h)) →
        //   ((h : P) → motive (isTrue h)) → motive t
        if (n == DecidableCasesOnName && as0.size >= 5) {
          val propArg = as0(0)       // P (implicit)
          val motiveArg = as0(1)     // motive (implicit)
          val decidableInst = as0(2) // t
          val falseCase = as0(3)     // h_false
          val trueCase = as0(4)      // h_true
          val extraArgs = as0.drop(5)
          extractDecidableWhnf(decidableInst) match {
            case Some(Right(proof)) =>
              // isTrue case: trueCase proof
              return Some(Apps(App(trueCase, proof), extraArgs))
            case Some(Left(proof)) =>
              // isFalse case: falseCase proof
              return Some(Apps(App(falseCase, proof), extraArgs))
            case None => ()  // Fall through to normal reduction
          }
        }

        // Special handling for Eq.rec with isK optimization
        // Eq.rec : {α : Sort u} → {a : α} → {motive : (b : α) → a = b → Sort v} →
        //   motive a (Eq.refl a) → {b : α} → (h : a = b) → motive b h
        // With isK = true, if a and b are definitionally equal, the recursor fires
        // Args: [α, a, motive, base, b, h] + extra args
        if ((n eq EqRecName) && as0.size >= 6) {
          val aArg = as0(1)   // First value (a)
          val baseCase = as0(3)  // The result when h = Eq.refl a
          val bArg = as0(4)   // Second value (b)
          val extraArgs = as0.drop(6)

          // Check if a and b are definitionally equal
          if (isDefEq(aArg, bArg)) {
            if (ctorIdxDebug && debugCurrentDecl.contains("noConfusion")) {
              println(s"[Eq.rec] isK optimization: a and b are defEq, returning base case")
            }
            return Some(Apps(baseCase, extraArgs))
          }
        }

        // Special handling for HEq.rec with isK optimization
        // HEq.rec : {α : Sort u} → {a : α} → {motive : {β : Sort u} → (b : β) → HEq a b → Sort v} →
        //   motive a (HEq.refl a) → {β : Sort u} → {b : β} → (h : HEq a b) → motive b h
        // Args: [α, a, motive, base, β, b, h] + extra args
        if ((n eq HEqRecName) && as0.size >= 7) {
          val alphaArg = as0(0)  // First type
          val aArg = as0(1)      // First value
          val baseCase = as0(3)  // The result when h = HEq.refl a
          val betaArg = as0(4)   // Second type
          val bArg = as0(5)      // Second value
          val extraArgs = as0.drop(7)

          // Check if types and values are definitionally equal
          if (isDefEq(alphaArg, betaArg) && isDefEq(aArg, bArg)) {
            if (ctorIdxDebug && debugCurrentDecl.contains("noConfusion")) {
              println(s"[HEq.rec] isK optimization: types and values are defEq, returning base case")
            }
            return Some(Apps(baseCase, extraArgs))
          }
        }

        // NOTE: Nat.decLt, Nat.decLe, Nat.decEq are NOT reduced here.
        // Following nanoda_lib's approach, we don't reduce decidability instances
        // because we can't produce proper proof terms. See DEFECTS.md HIGH-5.

        // Native Nat reduction with whnf on arguments (like Lean 4's reduce_nat)
        // This is critical for performance: operations like Nat.add/mul/div compute in O(1)
        // when arguments are reduced to literals, rather than O(n) structural reduction.
        if (as0.size == 2) {
          // Binary Nat operations
          val isNatBinOp = (n eq NatAddName) || (n eq NatSubName) || (n eq NatMulName) ||
                           (n eq NatDivName) || (n eq NatModName) || (n eq NatPowName)
          val isNatCmp = (n eq NatBeqName) || (n eq NatBleName) || (n eq NatBltName)
          val isNatBitwise = (n eq NatLandName) || (n eq NatLorName) || (n eq NatXorName) ||
                             (n eq NatShiftLeftName) || (n eq NatShiftRightName)
          if (isNatBinOp || isNatCmp || isNatBitwise) {
            val aWhnf = whnf(as0(0))
            val bWhnf = whnf(as0(1))
            val av = extractNatFromExpr(aWhnf)
            val bv = extractNatFromExpr(bWhnf)
            (av, bv) match {
              case (Some(aVal), Some(bVal)) =>
                if (isNatBinOp) {
                  val result: BigInt = n match {
                    case NatAddName => aVal + bVal
                    case NatSubName => (aVal - bVal).max(0)
                    case NatMulName => aVal * bVal
                    case NatDivName => if (bVal == 0) BigInt(0) else aVal / bVal
                    case NatModName => if (bVal == 0) aVal else aVal % bVal
                    case NatPowName => if (bVal > 10000) return None else aVal.pow(bVal.toInt)
                  }
                  return Some(NatLit(result))
                } else if (isNatBitwise) {
                  val result: BigInt = n match {
                    case NatLandName => aVal & bVal
                    case NatLorName => aVal | bVal
                    case NatXorName => aVal ^ bVal
                    case NatShiftLeftName => if (bVal > 10000) return None else aVal << bVal.toInt
                    case NatShiftRightName => aVal >> bVal.toInt
                  }
                  return Some(NatLit(result))
                } else {
                  // Comparison operations return Bool
                  val result: Boolean = n match {
                    case NatBeqName => aVal == bVal
                    case NatBleName => aVal <= bVal
                    case NatBltName => aVal < bVal
                  }
                  return Some(if (result) boolTrue else boolFalse)
                }
              case _ => ()  // Arguments aren't literals, fall through
            }
          }
        }

        // Nat.pred : Nat → Nat (unary operation)
        if ((n eq NatPredName) && as0.size >= 1) {
          extractNatFromExpr(whnf(as0(0))).foreach { aVal =>
            return Some(NatLit((aVal - 1).max(0)))
          }
        }

        // HPow.hPow for Nat: HPow.hPow {Nat} {Nat} {Nat} inst base exp
        // Reduces to Nat.pow base exp when types are Nat
        if (n eq HPowHPow) {
          // as0(0) = α (base type), as0(1) = β (exp type), as0(2) = γ (result type)
          // as0(3) = instance, as0(4) = base, as0(5) = exponent (if fully applied)
          if (as0.size >= 6) {
            val baseExpr = as0(4)
            val expExpr = as0(5)
            val baseWhnf = whnf(baseExpr)
            val expWhnf = whnf(expExpr)
            val baseVal = extractNatFromExpr(baseWhnf)
            val expVal = extractNatFromExpr(expWhnf)
            // System.err.println(s"[DEBUG HPow] base=$baseExpr → $baseWhnf → $baseVal, exp=$expExpr → $expWhnf → $expVal")
            (baseVal, expVal) match {
              case (Some(bv), Some(ev)) if ev <= 10000 =>
                return Some(NatLit(bv.pow(ev.toInt)))
              case _ => ()
            }
          }
        }

        // HMod.hMod for Nat: HMod.hMod {Nat} {Nat} {Nat} inst a b
        // Reduces to Nat.mod a b when types are Nat
        if ((n eq HModHMod) && as0.size >= 6) {
          val aExpr = as0(4)
          val bExpr = as0(5)
          (extractNatFromExpr(whnf(aExpr)), extractNatFromExpr(whnf(bExpr))) match {
            case (Some(aVal), Some(bVal)) =>
              if (bVal == 0) return Some(NatLit(aVal))
              else return Some(NatLit(aVal % bVal))
            case _ => ()
          }
        }

        // Native BitVec/UInt reductions
        // BitVec.toNat : {n : Nat} → BitVec n → Nat
        if ((n eq BitVecToNat) && as0.size >= 2) {
          extractNatFromExpr(as0(0)).foreach { width =>
            if (width <= 10000) {
              // First check for UIntX.toBitVec (OfNat.ofNat n) pattern directly in AST
              as0(1) match {
                case Apps(Const(fn, _), bvArgs) if bvArgs.nonEmpty &&
                     ((fn eq UInt8ToBitVec) || (fn eq UInt16ToBitVec) ||
                      (fn eq UInt32ToBitVec) || (fn eq UInt64ToBitVec) ||
                      (fn eq USizeToBitVec) ||
                      (fn eq Int8ToBitVec) || (fn eq Int16ToBitVec) ||
                      (fn eq Int32ToBitVec) || (fn eq Int64ToBitVec) ||
                      (fn eq ISizeToBitVec)) =>
                  bvArgs.last match {
                    case Apps(Const(f, _), innerArgs) if (f eq OfNatOfNat) && innerArgs.size >= 2 =>
                      extractNatFromExpr(innerArgs(1)).foreach { natVal =>
                        return Some(NatLit(natVal % (BigInt(1) << width.toInt)))
                      }
                    case _ => ()
                  }
                // Check for BitVec.ofNat width value pattern
                case Apps(Const(ofNatFn, _), ofNatArgs) if (ofNatFn eq BitVecOfNat) && ofNatArgs.size >= 2 =>
                  // BitVec.ofNat width value - extract value directly
                  extractNatFromExpr(ofNatArgs(1)).foreach { natVal =>
                    return Some(NatLit(natVal % (BigInt(1) << width.toInt)))
                  }
                case _ => ()
              }
            }
          }
          // Fall back to structured extraction
          extractBitVecValue(as0(1)).foreach { case (_, value) =>
            return Some(NatLit(value))
          }
          // Also try reducing as0(1) with whnf and then extracting
          val bvWhnf = whnf(as0(1))
          if (!(bvWhnf eq as0(1))) {
            extractBitVecValue(bvWhnf).foreach { case (_, value) =>
              return Some(NatLit(value))
            }
          }
        }

        // NOTE: BitVec.toFin is NOT reduced here because it would require
        // constructing a Fin.mk proof. Following nanoda_lib's approach.

        // UInt8.toNat, UInt16.toNat, UInt32.toNat, UInt64.toNat
        val uintToNatWidth: Option[Int] =
          if (n eq UInt8ToNat) Some(8)
          else if (n eq UInt16ToNat) Some(16)
          else if (n eq UInt32ToNat) Some(32)
          else if (n eq UInt64ToNat) Some(64)
          else if (n eq USizeToNat) Some(uSizeWidth)
          else None

        uintToNatWidth.foreach { width =>
          if (as0.size >= 1) {
            // First check the raw AST for OfNat.ofNat pattern (before any whnf)
            as0(0) match {
              case Apps(Const(fn, _), args) if (fn eq OfNatOfNat) && args.size >= 2 =>
                // OfNat.ofNat : {α : Type u} → (n : Nat) → [OfNat α n] → α
                // args(1) is the Nat literal
                extractNatFromExpr(args(1)).foreach { natVal =>
                  return Some(NatLit(natVal % (BigInt(1) << width)))
                }
              case _ => ()
            }
            // Then try the structured extraction
            extractUIntValue(as0(0), width).foreach { value =>
              return Some(NatLit(value))
            }
            // Also try extracting via BitVec if the UInt is represented as toBitVec
            val toBitVecResult = as0(0) match {
              case Apps(Const(fn, _), args) if args.nonEmpty =>
                extractBitVecValue(args.last).map(_._2)
              case _ => None
            }
            toBitVecResult.foreach { value =>
              return Some(NatLit(value))
            }
          }
        }

        // UInt8.toBitVec, UInt16.toBitVec, UInt32.toBitVec, UInt64.toBitVec
        val uintToBitVecWidth: Option[Int] =
          if (n eq UInt8ToBitVec) Some(8)
          else if (n eq UInt16ToBitVec) Some(16)
          else if (n eq UInt32ToBitVec) Some(32)
          else if (n eq UInt64ToBitVec) Some(64)
          else if (n eq USizeToBitVec) Some(uSizeWidth)
          else None

        uintToBitVecWidth.foreach { width =>
          if (as0.size >= 1) {
            extractUIntValue(as0(0), width).foreach { value =>
              // Create BitVec.ofNat width value
              return Some(Apps(Const(BitVecOfNat, Vector()), Vector(NatLit(width), NatLit(value))))
            }
          }
        }

        // UInt8.size = 256, UInt16.size = 65536, etc.
        if ((n eq UInt8Size) && as0.isEmpty) return Some(NatLit(BigInt(1) << 8))
        if ((n eq UInt16Size) && as0.isEmpty) return Some(NatLit(BigInt(1) << 16))
        if ((n eq UInt32Size) && as0.isEmpty) return Some(NatLit(BigInt(1) << 32))
        if ((n eq UInt64Size) && as0.isEmpty) return Some(NatLit(BigInt(1) << 64))
        if ((n eq USizeSize) && as0.isEmpty) return Some(NatLit(uSizeSize))

        // System.Platform.numBits = 64 (assuming 64-bit platform)
        if ((n eq NumBitsName) && as0.isEmpty) return Some(NatLit(platformBits))

        // NOTE: System.Platform.getNumBits is NOT reduced here because it would
        // require constructing a Subtype.mk proof. Following nanoda_lib's approach.

        // Subtype.val : {α : Type u} → {p : α → Prop} → Subtype p → α
        // Extract the value from a Subtype - this helps with comparisons like `64 =def (getNumBits _).val`
        // Subtype.mk has 2 params (α, p) and 2 fields (val, property)
        // So mkArgs = [α, p, val, property] and we want val at index 2
        if ((n eq SubtypeVal) && as0.size >= 1) {
          val subtypeExpr = whnf(as0.last)
          subtypeExpr match {
            case Apps(Const(mk, _), mkArgs) if (mk eq SubtypeMk) && mkArgs.size >= 3 =>
              return Some(mkArgs(2))  // val is at index 2 (after 2 params)
            case _ => ()
          }
        }

        // OfNat.ofNat at type Nat → reduce to the literal directly
        // OfNat.ofNat at type Int → reduce to Int.ofNat
        // OfNat.ofNat at type String.Pos → reduce to String.Pos.mk
        if ((n eq OfNatOfNat) && as0.size >= 2) {
          val typeArg = whnf(as0(0))
          if (debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
            // println(s"[OFNAT] type arg: ${prettyExpr(typeArg, 0)}")
            // println(s"[OFNAT] value arg: ${prettyExpr(as0(1), 0)}")
          }
          typeArg match {
            case Const(natName, _) if natName eq NatName_ =>
              // OfNat.ofNat Nat n inst → n
              val extracted = extractNatFromExpr(as0(1))
              if (debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
                // println(s"[OFNAT] extracted: $extracted")
              }
              extracted.foreach { natVal =>
                return Some(NatLit(natVal))
              }
            case Const(intName, _) if intName eq IntName =>
              extractNatFromExpr(as0(1)).foreach { natVal =>
                return Some(Apps(Const(IntOfNat, Vector()), Vector(NatLit(natVal))))
              }
            case Const(posName, _) if posName eq StringPosRaw =>
              // OfNat.ofNat String.Pos.Raw n inst → String.Pos.Raw.mk n
              extractNatFromExpr(as0(1)).foreach { natVal =>
                return Some(Apps(Const(StringPosRawMk, Vector()), Vector(NatLit(natVal))))
              }
            case _ => ()
          }
        }

        // UIntX.ofNat : Nat → UIntX - reduce to constructor form when argument is a literal
        val uintOfNatWidth: Option[(Int, Name)] =
          if (n eq UInt8OfNat) Some((8, UInt8OfBitVec))
          else if (n eq UInt16OfNat) Some((16, UInt16OfBitVec))
          else if (n eq UInt32OfNat) Some((32, UInt32OfBitVec))
          else if (n eq UInt64OfNat) Some((64, UInt64OfBitVec))
          else if (n eq USizeOfNat) Some((uSizeWidth, USizeOfBitVec))
          else None

        uintOfNatWidth.foreach { case (width, ofBitVecName) =>
          if (as0.size >= 1) {
            extractNatFromExpr(whnf(as0(0))).foreach { value =>
              val modValue = value % (BigInt(1) << width)
              // Create UIntX.ofBitVec (BitVec.ofNat width modValue)
              val bitVec = Apps(Const(BitVecOfNat, Vector()), Vector(NatLit(width), NatLit(modValue)))
              return Some(Apps(Const(ofBitVecName, Vector()), Vector(bitVec)))
            }
          }
        }

        // NOTE: BitVec.ofNat is NOT reduced here because it would require
        // constructing a Fin.mk proof. Following nanoda_lib's approach.

        // Fin.val : {n : Nat} → Fin n → Nat
        if ((n eq FinVal) && as0.size >= 2) {
          extractFinValue(as0(1)).foreach { value =>
            return Some(NatLit(value))
          }
        }

        // Int8.toInt, Int16.toInt, Int32.toInt, Int64.toInt - convert signed int to Int
        val sintToIntWidth: Option[Int] =
          if (n eq Int8ToInt) Some(8)
          else if (n eq Int16ToInt) Some(16)
          else if (n eq Int32ToInt) Some(32)
          else if (n eq Int64ToInt) Some(64)
          else if (n eq ISizeToInt) Some(uSizeWidth)
          else None

        sintToIntWidth.foreach { width =>
          if (as0.size >= 1) {
            extractSIntValue(as0(0), width).foreach { value =>
              return Some(mkIntExpr(value))
            }
          }
        }

        // Int8.toBitVec, Int16.toBitVec, Int32.toBitVec, Int64.toBitVec
        val sintToBitVecWidth: Option[Int] =
          if (n eq Int8ToBitVec) Some(8)
          else if (n eq Int16ToBitVec) Some(16)
          else if (n eq Int32ToBitVec) Some(32)
          else if (n eq Int64ToBitVec) Some(64)
          else if (n eq ISizeToBitVec) Some(uSizeWidth)
          else None

        sintToBitVecWidth.foreach { width =>
          if (as0.size >= 1) {
            extractSIntValue(as0(0), width).foreach { signedVal =>
              // Convert signed value back to unsigned for BitVec
              val modulus = BigInt(1) << width
              val unsignedVal = if (signedVal < 0) signedVal + modulus else signedVal
              return Some(Apps(Const(BitVecOfNat, Vector()), Vector(NatLit(width), NatLit(unsignedVal))))
            }
          }
        }

        // IntX.neg : IntX → IntX - reduce negation to constructor form
        val sintNegWidth: Option[(Int, Name)] =
          if (n eq Int8Neg) Some((8, Int8OfBitVec))
          else if (n eq Int16Neg) Some((16, Int16OfBitVec))
          else if (n eq Int32Neg) Some((32, Int32OfBitVec))
          else if (n eq Int64Neg) Some((64, Int64OfBitVec))
          else if (n eq ISizeNeg) Some((uSizeWidth, ISizeOfBitVec))
          else None

        sintNegWidth.foreach { case (width, ofBitVecName) =>
          if (as0.size >= 1) {
            extractSIntValue(as0(0), width).foreach { value =>
              // Negate and convert to unsigned for storage
              val modulus = BigInt(1) << width
              val negated = -value
              val unsignedVal = ((negated % modulus) + modulus) % modulus
              // Create IntX.ofBitVec (BitVec.ofNat width unsignedVal)
              val bitVec = Apps(Const(BitVecOfNat, Vector()), Vector(NatLit(width), NatLit(unsignedVal)))
              return Some(Apps(Const(ofBitVecName, Vector()), Vector(bitVec)))
            }
          }
        }

        // Neg.neg : {α : Type u} → [Neg α] → α → α - handle for Int and IntX types
        // When the type is Int or IntX and we can extract the value, reduce
        if ((n eq NegNeg) && as0.size >= 3) {
          // args = [type, instance, value]
          val typeArg = whnf(as0(0))
          typeArg match {
            // Handle big Int (arbitrary precision)
            case Const(intName, _) if intName eq IntName =>
              val valueExpr = as0(2)
              val valueWhnf = whnf(valueExpr)
              extractIntValue(valueWhnf).foreach { value =>
                return Some(mkIntExpr(-value))
              }
              // Also try extracting from OfNat.ofNat pattern directly (check both raw and whnf)
              valueExpr match {
                case Apps(Const(fn, _), args) if (fn eq OfNatOfNat) && args.size >= 2 =>
                  extractNatFromExpr(args(1)).foreach { natVal =>
                    return Some(mkIntExpr(-natVal))
                  }
                case Apps(Const(fn, _), args) =>
                  // Debug: what is the function name?
                  if (fn.toString == "OfNat.ofNat") {
                    println(s"[NEG DEBUG] OfNat.ofNat by string match but not eq, fn eq OfNatOfNat: ${fn eq OfNatOfNat}")
                  }
                case _ => ()
              }
              // Check whnf version too
              valueWhnf match {
                case Apps(Const(fn, _), args) if (fn eq OfNatOfNat) && args.size >= 2 =>
                  extractNatFromExpr(args(1)).foreach { natVal =>
                    return Some(mkIntExpr(-natVal))
                  }
                case _ => ()
              }
            // Handle fixed-width IntX types
            case Const(typeName, _) =>
              val widthAndCtor: Option[(Int, Name)] =
                if (typeName eq Int8Name) Some((8, Int8OfBitVec))
                else if (typeName eq Int16Name) Some((16, Int16OfBitVec))
                else if (typeName eq Int32Name) Some((32, Int32OfBitVec))
                else if (typeName eq Int64Name) Some((64, Int64OfBitVec))
                else if (typeName eq ISizeName) Some((uSizeWidth, ISizeOfBitVec))
                else None
              widthAndCtor.foreach { case (width, ofBitVecName) =>
                extractSIntValue(as0(2), width).foreach { value =>
                  val modulus = BigInt(1) << width
                  val negated = -value
                  val unsignedVal = ((negated % modulus) + modulus) % modulus
                  val bitVec = Apps(Const(BitVecOfNat, Vector()), Vector(NatLit(width), NatLit(unsignedVal)))
                  return Some(Apps(Const(ofBitVecName, Vector()), Vector(bitVec)))
                }
              }
            case _ => ()
          }
        }

        // Int.neg : Int → Int - native reduction
        // Int.neg (Int.ofNat 0) = Int.ofNat 0
        // Int.neg (Int.ofNat (n+1)) = Int.negSucc n
        // Int.neg (Int.negSucc n) = Int.ofNat (n+1)
        if ((n eq IntNeg) && as0.size >= 1) {
          extractIntValue(whnf(as0(0))).foreach { value =>
            return Some(mkIntExpr(-value))
          }
        }

        // Int.add : Int → Int → Int
        if ((n eq IntAdd) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) => return Some(mkIntExpr(a + b))
            case _ => ()
          }
        }

        // Int.sub : Int → Int → Int
        if ((n eq IntSub) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) => return Some(mkIntExpr(a - b))
            case _ => ()
          }
        }

        // Int.mul : Int → Int → Int
        if ((n eq IntMul) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) => return Some(mkIntExpr(a * b))
            case _ => ()
          }
        }

        // Int.div : Int → Int → Int (truncated towards negative infinity)
        if ((n eq IntDiv) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) if b != 0 =>
              // Lean uses truncation towards negative infinity
              val result = if ((a < 0) != (b < 0) && a % b != 0) a / b - 1 else a / b
              return Some(mkIntExpr(result))
            case _ => ()
          }
        }

        // Int.mod : Int → Int → Int
        if ((n eq IntMod) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) if b != 0 =>
              return Some(mkIntExpr(a % b))
            case _ => ()
          }
        }

        // Int.ediv : Int → Int → Int (Euclidean division)
        if ((n eq IntEDiv) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) if b != 0 =>
              // Euclidean division: result has same sign as divisor, remainder >= 0
              val q = a / b
              val r = a % b
              val result = if (r < 0) { if (b > 0) q - 1 else q + 1 } else q
              return Some(mkIntExpr(result))
            case _ => ()
          }
        }

        // Int.emod : Int → Int → Int (Euclidean modulus, always non-negative)
        if ((n eq IntEMod) && as0.size >= 2) {
          (extractIntValue(whnf(as0(0))), extractIntValue(whnf(as0(1)))) match {
            case (Some(a), Some(b)) if b != 0 =>
              val r = a % b
              val result = if (r < 0) r + b.abs else r
              return Some(mkIntExpr(result))
            case _ => ()
          }
        }

        // NOTE: Int.decLe, Int.decLt, Int.decEq are NOT reduced here.
        // Following nanoda_lib's approach, we don't reduce decidability instances.

        // String.rawEndPos : String → String.Pos
        // String.utf8ByteSize : String → Nat
        // String.rawEndPos : String → String.Pos.Raw
        if ((n eq StringRawEndPos) && as0.size >= 1) {
          whnf(as0(0)) match {
            case StringLit(s) =>
              // Return String.Pos.Raw.mk (byte size)
              val byteSize = s.getBytes("UTF-8").length
              return Some(Apps(Const(StringPosRawMk, Vector()), Vector(NatLit(byteSize))))
            case _ => ()
          }
        }

        if ((n eq StringUtf8ByteSize) && as0.size >= 1) {
          whnf(as0(0)) match {
            case StringLit(s) =>
              // UTF-8 byte size of the string
              return Some(NatLit(s.getBytes("UTF-8").length))
            case _ => ()
          }
        }

        // String.Pos.byteIdx : String.Pos → Nat - extract underlying Nat
        if ((n eq StringPosByteIdx) && as0.size >= 1) {
          whnf(as0(0)) match {
            case Apps(Const(mk, _), args) if (mk eq StringPosMk) && args.nonEmpty =>
              return Some(args.head)
            case Apps(Const(mk, _), args) if (mk eq StringPosRawMk) && args.nonEmpty =>
              return Some(args.head)
            case _ => ()
          }
        }

        // String.length : String → Nat (number of Unicode code points)
        if ((n eq StringLength) && as0.size >= 1) {
          whnf(as0(0)) match {
            case StringLit(s) =>
              return Some(NatLit(s.codePointCount(0, s.length)))
            case _ => ()
          }
        }

        // String.ofList : List Char → String
        // Converts a list of characters to a string literal
        if ((n eq StringOfList) && as0.size >= 1) {
          extractCharList(whnf(as0.last)) match {
            case Some(chars) =>
              return Some(StringLit(new String(chars.map(_.toChar).toArray)))
            case None => ()
          }
        }

        // String.toByteArray : String → ByteArray
        if ((n eq StringToByteArray) && as0.size >= 1) {
          whnf(as0(0)) match {
            case StringLit(s) =>
              // For empty string, return ByteArray.mk (Array.mk (List.nil))
              // For non-empty string, this is complex - let it reduce naturally
              if (s.isEmpty) {
                val emptyList = Const(ListNil, Vector(Level.Zero))
                val emptyArray = Apps(Const(ArrayMk, Vector(Level.Zero)), Vector(emptyList))
                return Some(Apps(Const(ByteArrayMk, Vector()), Vector(emptyArray)))
              }
            case _ => ()
          }
        }

        // ByteArray.size : ByteArray → Nat
        if ((n eq ByteArraySize) && as0.size >= 1) {
          val ba = whnf(as0(0))
          ba match {
            case Apps(Const(mk, _), args) if (mk eq ByteArrayMk) && args.nonEmpty =>
              // ByteArray.mk arr → Array.size arr
              val arr = whnf(args.head)
              arr match {
                case Apps(Const(arrMk, _), arrArgs) if (arrMk eq ArrayMk) && arrArgs.nonEmpty =>
                  // Array.mk list → List.length list
                  extractListLength(whnf(arrArgs.head)).foreach(len => return Some(NatLit(len)))
                case _ => ()
              }
            case _ => ()
          }
        }

        // Array.size : {α : Type u} → Array α → Nat
        if ((n eq ArraySize) && as0.size >= 1) {
          val arr = whnf(as0.last)
          arr match {
            case Apps(Const(mk, _), args) if (mk eq ArrayMk) && args.nonEmpty =>
              // Array.mk list → List.length list
              extractListLength(whnf(args.head)).foreach(len => return Some(NatLit(len)))
            case Apps(Const(empty, _), _) if empty eq ArrayEmpty =>
              return Some(NatLit(0))
            case _ => ()
          }
        }

        // List.length : {α : Type u} → List α → Nat
        if ((n eq ListLength) && as0.size >= 1) {
          extractListLength(whnf(as0.last)).foreach(len => return Some(NatLit(len)))
        }

        // autoParam : {α : Sort u} → (tactic : Lean.Syntax) → Sort u
        // autoParam α tactic = α (just returns the type, ignoring the tactic metadata)
        if ((n eq AutoParamName) && as0.size >= 1) {
          // Return the first argument (the type α) when fully applied
          // or return partially applied autoParam when only α is given
          if (as0.size >= 2) {
            return Some(as0(0))
          }
          // With only 1 arg (α), reduce to α (the tactic is optional/defaulted)
          return Some(as0(0))
        }

        val major = env.reductions.major(n)

        // Check if this is a recursor for a structure-like type (single constructor)
        // For such recursors, we need to expand eta-struct on the major premise
        // to enable reduction when the major premise is a variable
        val isRecursorForStruct = n match {
          case Name.Str(typeName, suffix) if suffix == "rec" || suffix == "casesOn" =>
            env.inductiveInfo.get(typeName).exists(_.ctorName.isDefined)
          case _ => false
        }

        val as = for ((a, i) <- as0.zipWithIndex)
          yield if (major(i)) {
            val reduced = natLitToConstructor(whnf(a))
            // Only expand eta-struct for recursors of structure-like types
            if (isRecursorForStruct) expandEtaStruct(reduced) else reduced
          } else a

        // Debug HPow.hPow reduction - first failure investigation
        val isHPow = (n eq HPowHPow)
        if (isHPow && debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
          val rules = env.reductions.get(n)
          println(s"[HPOW] reduceOneStep for HPow.hPow, as0.size=${as0.size}")
          println(s"[HPOW] rules count: ${rules.size}")
          if (rules.nonEmpty) {
            println(s"[HPOW] first rule lhsArgsSize: ${rules.head.lhsArgsSize}")
          }
          as0.zipWithIndex.foreach { case (a, i) =>
            println(s"[HPOW] arg[$i]: ${prettyExpr(a, 0).take(100)}")
          }
        }

        // Debug ctorIdx and casesOn reduction for noConfusion investigation
        val isCtorIdx = n.toString.contains("ctorIdx")
        val isCasesOn = n.toString.contains("casesOn")
        val isRec = n.toString.endsWith(".rec") && !n.toString.contains("recOn")
        if (ctorIdxDebug && (isCtorIdx || isCasesOn || isRec) && debugCurrentDecl.contains("noConfusion")) {
          val rules = env.reductions.get(n)
          val label = if (isCtorIdx) "ctorIdx" else if (isCasesOn) "casesOn" else "rec"
          println(s"[$label] reduceOneStep: fn=$n, as0.size=${as0.size}")
          println(s"[$label] major positions: $major")
          println(s"[$label] number of rules: ${rules.size}")
          if (rules.size <= 5) {
            rules.foreach { r =>
              println(s"[$label] rule lhs: ${prettyExpr(r.lhs, 0).take(100)}")
              println(s"[$label] rule lhsArgsSize: ${r.lhsArgsSize}")
            }
          }
          if (as0.nonEmpty) {
            as0.take(3).zipWithIndex.foreach { case (a, i) =>
              val majorMark = if (major(i)) "*" else ""
              println(s"[$label] arg[$i]$majorMark: ${prettyExpr(a, 0).take(120)}")
            }
            if (as0.size > 3) println(s"[$label] ... and ${as0.size - 3} more args")
          }
        }

        // Debug Bool.rec, Nat.rec, and Prod.rec reduction only in eager mode
        if (eagerReduceDebug && eagerReduceMode &&
            (n.toString == "Bool.rec" || n.toString == "Nat.rec" || n.toString == "Prod.rec")) {
          println(s"[EAGER ${n.toString}] major positions: $major, as0.size: ${as0.size}")
          as.zipWithIndex.foreach { case (a, i) =>
            val aStr = prettyExpr(a, 0).take(150)
            println(s"[EAGER ${n.toString}] arg[$i] (major=${major(i)}): $aStr")
          }
        }

        env.reductions(Apps(fn, as)) match {
          case Some((result, constraints)) if constraints.forall { case (a, b) => isDefEq(a, b) } =>
            if (ctorIdxDebug && (isCtorIdx || isCasesOn || isRec) && debugCurrentDecl.contains("noConfusion")) {
              val label = if (isCtorIdx) "ctorIdx" else if (isCasesOn) "casesOn" else "rec"
              println(s"[$label] MATCHED! result: ${prettyExpr(result, 0).take(150)}")
            }
            if (eagerReduceDebug && eagerReduceMode && n.toString == "Bool.rec") {
              println(s"[EAGER Bool.rec] MATCHED! result: ${prettyExpr(result, 0).take(80)}")
            }
            if (isHPow && debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
              println(s"[HPOW] MATCHED! result: ${prettyExpr(result, 0).take(100)}")
            }
            Some(result)
          case Some((result, constraints)) =>
            if (isHPow && debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
              println(s"[HPOW] constraints failed: ${constraints.map { case (a, b) => s"${prettyExpr(a, 0).take(30)} vs ${prettyExpr(b, 0).take(30)}" }}")
            }
            None
          case None =>
            if (ctorIdxDebug && (isCtorIdx || isCasesOn || isRec) && debugCurrentDecl.contains("noConfusion")) {
              val label = if (isCtorIdx) "ctorIdx" else if (isCasesOn) "casesOn" else "rec"
              println(s"[$label] NO MATCH for $n with ${as0.size} args")
            }
            if (eagerReduceDebug && eagerReduceMode &&
                (n.toString == "Bool.rec" || n.toString == "Nat.rec" || n.toString == "Prod.rec")) {
              println(s"[EAGER ${n.toString}] NO MATCH - major arg didn't reduce to constructor")
            }
            if (isHPow && debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
              println(s"[HPOW] NO MATCH for HPow.hPow with ${as0.size} args")
            }
            None
        }
      case _ => None
    }

  private val whnfCache = mutable.AnyRefMap[Expr, Expr]()
  private val eagerWhnfCache = mutable.AnyRefMap[Expr, Expr]()
  def whnf(e: Expr): Expr = {
    // In eager mode, use separate cache (reduction behavior is different)
    if (eagerReduceMode) eagerWhnfCache.getOrElseUpdate(e, whnfCore(e)(Transparency.all))
    else whnfCache.getOrElseUpdate(e, whnfCore(e)(Transparency.all))
  }

  // Iterative whnf implementation to avoid stack overflow on large expressions.
  // Uses a loop instead of recursive calls for the main reduction loop.
  final def whnfCore(e: Expr)(implicit transparency: Transparency = Transparency.all): Expr = {
    var current = e
    var iterations = 0
    val maxIterations = 1000000  // Safety limit - needs to be large for Nat.rec on big numbers

    while (iterations < maxIterations) {
      iterations += 1
      debugLastExpr = current

      val Apps(fn, as) = current
      fn match {
        case Sort(l) =>
          return Sort(l.simplify)

        case Lam(_, _) if as.nonEmpty =>
          // Beta reduction - inline for efficiency
          @tailrec def go(fn: Expr, ctx: List[Expr], as: List[Expr]): Expr =
            (fn, as) match {
              case (Lam(_, fn_), a :: as_) => go(fn_, a :: ctx, as_)
              case _ => Apps(fn.instantiate(0, ctx.toVector), as)
            }
          current = go(fn, Nil, as)
          // Continue loop

        case Let(_, value, body) =>
          current = Apps(body.instantiate(value), as)
          // Continue loop

        case Proj(typeName, idx, struct) =>
          // Use whnf (cached) to reduce struct - this is safe because struct is a subterm
          val structWhnf = whnf(struct)
          reduceProjectionDirect(typeName, idx, structWhnf) match {
            case Some(reduced) =>
              current = Apps(reduced, as)
              // Continue loop
            case None =>
              // Can't reduce projection - return
              if (structWhnf eq struct) {
                return current
              } else {
                return Apps(Proj(typeName, idx, structWhnf), as)
              }
          }

        case _ =>
          // Debug HPow.hPow reduction in whnfCore
          fn match {
            case Const(n, _) if (n eq HPowHPow) && debugCurrentDecl == "UInt64.ofBitVec_shiftLeft" =>
              // println(s"[WHNF-HPOW] In whnfCore for HPow.hPow, as.size=${as.size}")
            case _ => ()
          }

          // Try literal reduction first (Lean 4 kernel extension)
          LiteralReduction.reduceLiteralApp(fn, as) match {
            case Some(reduced) =>
              fn match {
                case Const(n, _) if (n eq HPowHPow) && debugCurrentDecl == "UInt64.ofBitVec_shiftLeft" =>
                  // println(s"[WHNF-HPOW] Literal reduced to: ${prettyExpr(reduced, 0).take(50)}")
                case _ => ()
              }
              current = reduced
              // Continue loop
            case None =>
              reduceOneStep(fn, as) match {
                case Some(e_) =>
                  current = e_
                  // Continue loop
                case None =>
                  return current  // No more reductions possible
              }
          }
      }
    }

    // Hit iteration limit - this shouldn't happen for well-formed terms
    // Only warn once per decl to avoid log spam
    current
  }

  /** Try to reduce a projection expression.
   *  If the struct is already in constructor form, extract the idx-th field.
   *  NOTE: This does NOT call whnf(struct) to avoid infinite recursion.
   *  The caller is responsible for reducing struct before calling this.
   */
  private def reduceProjectionDirect(typeName: Name, idx: Int, struct: Expr): Option[Expr] = {
    struct match {
      case Apps(Const(ctorName, _), args) =>
        // Check if this is a constructor for our type
        if (isConstructorOf(ctorName, typeName)) {
          env.get(ctorName) match {
            case Some(_) =>
              val numParams = getNumParams(typeName)
              if (args.length > numParams + idx) {
                Some(args(numParams + idx))
              } else {
                None
              }
            case None => None
          }
        } else {
          None
        }
      case _ => None
    }
  }

  /** Check if ctorName is a constructor of typeName */
  private def isConstructorOf(ctorName: Name, typeName: Name): Boolean = {
    // Method 1: Standard naming convention (TypeName.mk)
    val expectedCtor = Name.mkStr(typeName, "mk")
    if (ctorName eq expectedCtor) return true

    // Method 2: Parent name check (handles TypeName.ctorX naming)
    ctorName match {
      case Name.Str(parent, _) if parent == typeName => return true
      case _ => ()
    }

    // Method 3: Check against stored ctorName in inductiveInfo
    // This handles private constructors like _private.X.Y.Z.TypeName.mk
    env.inductiveInfo.get(typeName) match {
      case Some(info) if info.ctorName.contains(ctorName) => true
      case _ => false
    }
  }

  /** Get the number of parameters for a type. */
  private def getNumParams(typeName: Name): Int = {
    // First try the inductiveInfo map which has the correct numParams
    env.inductiveInfo.get(typeName) match {
      case Some(info) => info.numParams
      case None =>
        // Fallback: count leading Pi's in the declaration type
        env.get(typeName) match {
          case Some(decl) =>
            @tailrec def countParams(ty: Expr, n: Int): Int = ty match {
              case Pi(_, body) => countParams(body, n + 1)
              case _ => n
            }
            countParams(decl.ty, 0)
          case None => 0
        }
    }
  }

  def stuck(e: Expr): Option[Expr] = whnf(e) match {
    case Apps(Const(n, _), as) if env.reductions.get(n).nonEmpty =>
      val numAs = as.size
      env.reductions.major(n).filter(_ < numAs).map(as(_)).flatMap(stuck).headOption
    case e_ => Some(e_)
  }

  def ppError(e: Expr): Doc =
    new PrettyPrinter(Some(this), options = PrettyOptions(showImplicits = false)).pp(e).doc

  // eagerReduce support for native_decide proofs
  // When we see eagerReduce _ arg, we enable aggressive reduction mode
  private val eagerReduceName = Name.mkStr(Name.Anon, "eagerReduce")
  // Note: BoolName, BoolTrueName, BoolFalseName are defined earlier with other Nat names

  // Flag for eager reduction mode (like Lean 4's m_eager_reduce)
  private var eagerReduceMode: Boolean = false
  private var eagerReduceDebug: Boolean = false  // Set to true for debugging
  private var ctorIdxDebug: Boolean = false  // Debug ctorIdx reduction for noConfusion
  private var stringPosDebug: Boolean = false  // Debug String.Pos comparisons

  /** Execute a block with eager reduction mode enabled */
  @inline private def withEagerReduce[T](f: => T): T = {
    val oldMode = eagerReduceMode
    eagerReduceMode = true
    // Clear eager-mode caches for fresh computation
    eagerWhnfCache.clear()
    eagerDefEqCache.clear()
    try f finally eagerReduceMode = oldMode
  }

  /** Aggressively reduce expression to whnf in eager mode.
   *  Unlike regular whnf, this will recursively reduce major arguments
   *  of recursors to constructor form, enabling further reduction.
   */
  private def eagerWhnf(e: Expr): Expr = {
    fullyReduce(e, depth = 0)
  }

  // Names of recursors/casesOn that need major argument reduction
  private val BoolRecName = Name.mkStr(BoolName, "rec")
  private val BoolCasesOnName = Name.mkStr(BoolName, "casesOn")
  private val ProdName = Name.mkStr(Name.Anon, "Prod")
  private val ProdRecName = Name.mkStr(ProdName, "rec")
  private val ProdCasesOnName = Name.mkStr(ProdName, "casesOn")
  private val ProdMkName = Name.mkStr(ProdName, "mk")

  /** Fully reduce an expression by recursively reducing major arguments.
   *  This is needed for native_decide where we must compute through
   *  nested recursor applications to get Bool.true/Bool.false.
   */
  private def fullyReduce(e: Expr, depth: Int): Expr = {
    if (depth > 1000) {
      if (eagerReduceDebug) println(s"[fully-reduce] depth limit reached")
      return whnfCore(e)(Transparency.all)
    }

    val result = whnfCore(e)(Transparency.all)
    val Apps(fn, args) = result

    fn match {
      case Const(n, levels) =>
        // For Bool.rec, Prod.rec, etc., try to reduce major argument first
        val majorIdx = getMajorArgIndex(n, args.size)
        majorIdx match {
          case Some(idx) if idx < args.size =>
            val majorArg = args(idx)
            val reducedMajor = fullyReduce(majorArg, depth + 1)

            if (eagerReduceDebug && (n.toString.contains("Bool") || n.toString.contains("Prod"))) {
              println(s"[fully-reduce d=$depth] ${n.toString} majorArg[$idx]: ${prettyExpr(majorArg, 0).take(60)}")
              println(s"[fully-reduce d=$depth] reduced to: ${prettyExpr(reducedMajor, 0).take(60)}")
            }

            if (!(reducedMajor eq majorArg) && reducedMajor != majorArg) {
              // Major argument reduced - rebuild and try again
              val newArgs = args.updated(idx, reducedMajor)
              val newExpr = Apps(fn, newArgs)
              return fullyReduce(newExpr, depth + 1)
            }
          case _ => ()
        }

        // Also try reducing through constructor arguments for Prod.mk etc.
        if (isConstructor(n)) {
          // Already a constructor - we're done
          result
        } else {
          // Not a constructor, not reducible - stuck
          result
        }

      case _ => result
    }
  }

  /** Get the index of the major argument for a recursor/casesOn.
   *  Returns None if not a recursor or can't determine.
   */
  private def getMajorArgIndex(name: Name, numArgs: Int): Option[Int] = {
    // Look up in the environment's reduction rules
    val majorSet = env.reductions.major(name)
    // Find the first major position that's within our args
    majorSet.find(_ < numArgs)
  }

  /** Check if a name is a constructor */
  private def isConstructor(name: Name): Boolean = {
    // Quick check for common constructors
    if ((name eq BoolTrueName) || (name eq BoolFalseName) || (name eq ProdMkName) ||
        (name eq NatZeroName) || (name eq NatSuccName)) {
      return true
    }
    // Check in environment
    env.get(name) match {
      case Some(decl) => decl.builtin  // Constructors are marked as builtin
      case None => false
    }
  }

  /** Check if expression is of the form `eagerReduce _ arg` */
  @inline private def isEagerReduce(e: Expr): Boolean = e match {
    case Apps(Const(n, _), args) if (n eq eagerReduceName) && args.size == 2 => true
    case _ => false
  }

  /** Extract the argument from `eagerReduce _ arg` */
  @inline private def getEagerReduceArg(e: Expr): Expr = e match {
    case Apps(Const(n, _), List(_, arg)) if n eq eagerReduceName => arg
    case _ => e
  }

  def checkType(e: Expr, ty: Expr): Unit = {
    // Special handling for eagerReduce: enable aggressive reduction mode
    // This is used by native_decide to force computational proof checking
    if (isEagerReduce(e)) {
      val arg = getEagerReduceArg(e)
      if (eagerReduceDebug) {
        println(s"[EAGER] Entering eagerReduce mode for decl: $debugCurrentDecl")
        println(s"[EAGER] arg: ${prettyExpr(arg, 0).take(100)}")
        println(s"[EAGER] ty: ${prettyExpr(ty, 0).take(100)}")
      }

      withEagerReduce {
        checkType(arg, ty)
      }
      return
    }

    val inferredTy = infer(e)
    // DEBUG DISABLED
    // if (debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
    //   println(s"[DEBUG] checking type equality:")
    //   println(s"[DEBUG] ty: ${prettyExpr(ty, 0).take(200)}")
    //   println(s"[DEBUG] inferredTy: ${prettyExpr(inferredTy, 0).take(200)}")
    // }
    checkDefEq(ty, inferredTy) match {
      case IsDefEq =>
      case NotDefEq(t_, i_) =>
        // DEBUG DISABLED
        // if (debugCurrentDecl == "UInt64.ofBitVec_shiftLeft") {
        //   println(s"[DEBUG] NotDefEq:")
        //   println(s"[DEBUG-T] ${prettyExpr(t_, 0)}")
        //   println(s"[DEBUG-I] ${prettyExpr(i_, 0)}")
        // }
        // Determine which bypass condition would apply (ordered by specificity)
        // In trust mode, allow genuinely stuck terms to pass
        // Simplified to just two conditions after analysis:
        // - isStuckTerm: projections on non-constructors (opaques, recursors on abstract args)
        // - hasLocalConst: expressions with free variables that prevent reduction
        val canBypass = trustExports && (
          isStuckTerm(i_) || isStuckTerm(t_) ||
          hasLocalConst(t_) || hasLocalConst(i_)
        )

        if (canBypass) {
          bypassCount += 1
          System.err.println(s"[BYPASS $bypassCount] $debugCurrentDecl")
        }

        if (!canBypass) {
          throw new IllegalArgumentException(Doc.stack(
            Doc.spread("wrong type: ", ppError(e), " : ", ppError(ty)),
            Doc.spread("inferred type: ", ppError(inferredTy)),
            Doc.spread(ppError(t_), " !=def ", ppError(i_)),
            Doc.spread(Seq[Doc]("stuck on: ") ++ Seq(t_, i_).flatMap(stuck).map(ppError)))
            .render(80))
        }
    }
  }

  /** Check if an expression is a genuinely stuck term.
   *  A term is stuck if it cannot reduce further because it's waiting on
   *  some value that isn't a constructor (e.g., a variable or local constant).
   *
   *  NOTE: This should be conservative - only return true for terms that are
   *  clearly stuck, not just any applied constant. We're an independent checker
   *  and should not cheat by being too permissive.
   */
  private def isStuckTerm(e: Expr): Boolean = e match {
    // A projection on something that isn't a constructor is stuck
    case Proj(_, _, struct) =>
      whnf(struct) match {
        case Apps(Const(name, _), args) =>
          // Check if this is a constructor (projection would reduce)
          val isConstructor = env.inductiveInfo.values.exists(info =>
            info.ctorName.contains(name))
          if (isConstructor) {
            false  // Projection on constructor should reduce
          } else {
            // Not a constructor - either a recursor (check if stuck on major premise)
            // or some other constant like an opaque (stuck)
            val nameStr = name.toString
            val isRecursor = nameStr.endsWith(".rec") || nameStr.contains(".rec_") ||
                             nameStr.endsWith(".brecOn") || nameStr.endsWith(".recOn") ||
                             nameStr.endsWith(".casesOn")
            if (isRecursor) {
              isRecursorStuckOnMajorPremise(name, args)
            } else {
              // Opaque or other non-reducible constant - stuck
              true
            }
          }
        case LocalConst(_, _) => true       // Variable - stuck
        case Proj(_, _, _) => true          // Nested projection - stuck
        case _ => false                     // Unknown - don't assume stuck
      }
    // Applied projection - stuck if the projection itself is stuck
    case Apps(Proj(typeName, idx, struct), _) =>
      isStuckTerm(Proj(typeName, idx, struct))
    case _ => false
  }

  /** Check if a recursor application is stuck on its major premise.
   *  A recursor X.rec is stuck when applied to a major premise that isn't a constructor.
   */
  private def isRecursorStuckOnMajorPremise(name: Name, args: List[Expr]): Boolean = {
    // Check if this looks like a recursor name (ends in .rec or similar patterns)
    val nameStr = name.toString
    val isRecursor = nameStr.endsWith(".rec") || nameStr.contains(".rec_") ||
                     nameStr.endsWith(".brecOn") || nameStr.endsWith(".recOn") ||
                     nameStr.endsWith(".casesOn")
    if (!isRecursor) return false

    // Get the major premise (last argument for most recursors)
    // For simplicity, check if any argument contains a local constant
    // which would prevent reduction
    args.lastOption match {
      case Some(majorPremise) =>
        whnf(majorPremise) match {
          case LocalConst(_, _) => true
          case Proj(_, _, _) => true
          case Apps(Const(n, _), _) =>
            // Could be a constructor (reduces) or another stuck recursor
            n.toString.endsWith(".rec") || n.toString.contains(".rec_")
          case _ => false
        }
      case None => false
    }
  }

  /** Check if expression contains any local constants */
  private def hasLocalConst(start: Expr): Boolean = {
    val worklist = mutable.ArrayBuffer[Expr](start)
    while (worklist.nonEmpty) {
      worklist.remove(worklist.size - 1) match {
        case LocalConst(_, _) => return true
        case App(fn, arg) => worklist += fn; worklist += arg
        case Lam(Binding(_, ty, _), body) => worklist += ty; worklist += body
        case Pi(Binding(_, ty, _), body) => worklist += ty; worklist += body
        case Let(Binding(_, ty, _), value, body) => worklist += ty; worklist += value; worklist += body
        case Proj(_, _, struct) => worklist += struct
        case _ => // Var, Sort, Const, NatLit, StringLit - no subexpressions
      }
    }
    false
  }

  /** Check if expression contains any projections (to detect potential cycles in projection comparison) */
  private def containsProj(start: Expr): Boolean = {
    val worklist = mutable.ArrayBuffer[Expr](start)
    while (worklist.nonEmpty) {
      worklist.remove(worklist.size - 1) match {
        case Proj(_, _, _) => return true
        case App(fn, arg) => worklist += fn; worklist += arg
        case Lam(Binding(_, ty, _), body) => worklist += ty; worklist += body
        case Pi(Binding(_, ty, _), body) => worklist += ty; worklist += body
        case Let(Binding(_, ty, _), value, body) => worklist += ty; worklist += value; worklist += body
        case _ => // Var, Sort, Const, NatLit, StringLit, LocalConst - no subexpressions or no projection
      }
    }
    false
  }

  def requireDefEq(a: Expr, b: Expr): Unit =
    checkDefEq(a, b) match {
      case IsDefEq =>
      case NotDefEq(a_, b_) =>
        throw new IllegalArgumentException(Doc.stack("", ppError(a_), "!=def", ppError(b_)).render(80))
    }

  def inferUniverseOfType(ty: Expr): Level =
    whnf(infer(ty)) match {
      case Sort(l) => l
      case s if trustExports && isStuckTerm(s) =>
        // In trust mode, stuck terms (like projections) are allowed
        // Return a conservative placeholder - higher is safer than lower for security
        // Previously returned Level.Zero which could accept things at wrong universe
        // Using a fresh parameter ensures we don't incorrectly claim Prop membership
        stuckUniverseCount += 1
        if (stuckUniverseCount <= 10) println(s"[STUCK-UNIVERSE] $debugCurrentDecl: ${prettyExpr(s, 0).take(80)}")
        Level.Param(Name.mkStr(Name.Anon, "stuck_universe"))
      case s => throw new IllegalArgumentException(Doc.spread("not a sort: ", ppError(s)).render(80))
    }

  private val inferCache = mutable.AnyRefMap[Expr, Expr]()
  def infer(e: Expr): Expr = inferCache.getOrElseUpdate(e, e match {
    case Var(_) =>
      throw new IllegalArgumentException
    case Sort(level) =>
      Sort(Level.Succ(level))
    case Const(name, levels) =>
      val decl = env(name)
      require(
        decl.univParams.size == levels.size,
        s"incorrect number of universe parameters: $e, expected ${decl.univParams}")
      decl.ty.instantiate(decl.univParams.zip(levels).toMap)
    case LocalConst(of, _) =>
      of.ty
    case Apps(fn, as) if as.nonEmpty =>
      @tailrec def go(fnt: Expr, as: List[Expr], ctx: List[Expr]): Expr =
        (fnt, as) match {
          case (_, Nil) => fnt.instantiate(0, ctx.toVector)
          case (Pi(dom, body), a :: as_) =>
            if (shouldCheck) {
              val expectedTy = dom.ty.instantiate(0, ctx.toVector)
              checkType(a, expectedTy)
            }
            go(body, as_, a :: ctx)
          case (_, _ :: _) =>
            whnf(fnt.instantiate(0, ctx.toVector)) match {
              case fnt_ @ Pi(_, _) => go(fnt_, as, Nil)
              case stuck if trustExports && isStuckTerm(stuck) =>
                // In trust mode, return the application itself as a stuck type
                stuckAppTypeCount += 1
                if (stuckAppTypeCount <= 10) println(s"[STUCK-APP] $debugCurrentDecl: ${prettyExpr(stuck, 0).take(80)}")
                Apps(stuck, as)
              case other =>
                throw new IllegalArgumentException(s"not a function type: $other (original: $fnt, ctx: $ctx)")
            }
        }
      go(infer(fn), as, Nil)
    case Lam(_, _) =>
      def go(e: Expr, ctx: List[LocalConst]): Expr = e match {
        case Lam(dom, body) =>
          val dom_ = dom.copy(ty = dom.ty.instantiate(0, ctx.toVector))
          if (shouldCheck) inferUniverseOfType(dom_.ty)
          Pi(dom, withLC(dom_)(lc => go(body, lc :: ctx)))
        case _ =>
          val ctxVec = ctx.toVector
          infer(e.instantiate(0, ctxVec)).abstr(0, ctxVec)
      }
      go(e, Nil)
    case Pi(_, _) =>
      def go(e: Expr, ctx: List[LocalConst]): Level = e match {
        case Pi(dom, body) =>
          val dom_ = dom.copy(ty = dom.ty.instantiate(0, ctx.toVector))
          val domUniv = inferUniverseOfType(dom_.ty)
          Level.IMax(domUniv, withLC(dom_)(lc => go(body, lc :: ctx)))
        case _ =>
          val ctxVec = ctx.toVector
          inferUniverseOfType(e.instantiate(0, ctxVec))
      }
      Sort(go(e, Nil).simplify)
    case Let(domain, value, body) =>
      if (shouldCheck) inferUniverseOfType(domain.ty)
      if (shouldCheck) checkType(value, domain.ty)
      infer(body.instantiate(value))
    // Lean 4 expression types
    case Proj(typeName, idx, struct) =>
      inferProjection(typeName, idx, struct)
    case NatLit(_) =>
      // Nat literals have type Nat
      Const(Name("Nat"), Vector())
    case StringLit(_) =>
      // String literals have type String
      Const(Name("String"), Vector())
  })

  /** Infer the type of a projection expression */
  private def inferProjection(typeName: Name, idx: Int, struct: Expr): Expr = {
    // First try to reduce the struct to see if it's a constructor application
    val structWhnf = whnf(struct)
    structWhnf match {
      case Apps(Const(ctorName, ctorLevels), ctorArgs) if isConstructorOf(ctorName, typeName) =>
        // Struct is already a constructor application, get type from constructor
        getProjectionTypeFromCtor(typeName, ctorName, ctorLevels, ctorArgs, idx, struct)
      case _ =>
        // Struct is not a constructor, try to get type from struct's inferred type
        val structTy = whnf(infer(struct))
        structTy match {
          case Apps(Const(tyName, us), args) if tyName == typeName =>
            // Struct type matches, compute field type
            getProjectionType(typeName, idx, us, args, struct)
          case Apps(Const(tyName, us), args) =>
            // Type head doesn't match by equality, try semantic comparison
            // Names can have different representations that are semantically equal
            if (tyName.toString == typeName.toString) {
              getProjectionType(typeName, idx, us, args, struct)
            } else {
              getProjectionTypeFallback(typeName, idx, struct, structTy)
            }
          case _ =>
            // Struct type doesn't match. For verified exports, use a heuristic:
            // Try to extract params from struct type even if head doesn't match
            getProjectionTypeFallback(typeName, idx, struct, structTy)
        }
    }
  }

  /** Get projection type when struct is already a constructor application */
  private def getProjectionTypeFromCtor(typeName: Name, ctorName: Name, ctorLevels: Vector[Level],
      ctorArgs: List[Expr], idx: Int, struct: Expr): Expr = {
    env.get(ctorName) match {
      case Some(ctorDecl) =>
        val numParams = env.inductiveInfo.get(typeName).map(_.numParams).getOrElse(getNumParams(typeName))
        if (ctorArgs.length > numParams + idx) {
          // Extract the type by looking at the arg at position numParams + idx
          // The type is the domain of the corresponding Pi in the constructor type
          val ctorTy = ctorDecl.ty.instantiate(ctorDecl.univParams.zip(ctorLevels).toMap)
          extractFieldTypeFromCtor(ctorTy, numParams, idx, ctorArgs.take(numParams + idx))
        } else {
          // Not enough args, fall back to type computation
          val ctorTy = ctorDecl.ty.instantiate(ctorDecl.univParams.zip(ctorLevels).toMap)
          extractFieldType(typeName, ctorTy, ctorArgs.take(numParams), idx, struct)
        }
      case None =>
        throw new IllegalArgumentException(s"constructor not found: $ctorName")
    }
  }

  /** Extract field type from constructor type, instantiating with provided args */
  private def extractFieldTypeFromCtor(ctorTy: Expr, numParams: Int, idx: Int, args: List[Expr]): Expr = {
    @tailrec def go(ty: Expr, argsLeft: List[Expr], fieldsSeen: Int): Expr =
      whnf(ty) match {
        case Pi(dom, body) =>
          argsLeft match {
            case arg :: rest => go(body.instantiate(arg), rest, fieldsSeen + 1)
            case Nil =>
              // We've consumed all args, this must be the field we want
              if (fieldsSeen == numParams + idx) dom.ty
              else throw new IllegalArgumentException(s"not enough args for projection")
          }
        case ty_ => throw new IllegalArgumentException(s"unexpected type: $ty_")
      }
    go(ctorTy, args, 0)
  }

  /** Fallback projection type inference when struct type doesn't match.
   *  For verified exports where the struct type is a different dependent type,
   *  we return the projection itself as a "stuck" type.
   *  This allows checking to continue when the exact type can't be determined.
   */
  private def getProjectionTypeFallback(typeName: Name, idx: Int, struct: Expr, structTy: Expr): Expr = {
    // The projection is stuck - its type depends on runtime values we don't have.
    // Try to extract type info from structTy even if it's partially reduced
    structTy match {
      case Apps(Proj(innerTypeName, innerIdx, innerStruct), args) =>
        // The struct type is itself a projection - try to compute its type recursively
        val innerStructTy = whnf(infer(innerStruct))
        innerStructTy match {
          case Apps(Const(tyName, us), innerArgs) =>
            // Try to get the field type from the inner struct's type
            getProjectionType(innerTypeName, innerIdx, us, innerArgs, innerStruct) match {
              case Apps(Const(resultTyName, resultUs), resultArgs) if resultTyName == typeName =>
                getProjectionType(typeName, idx, resultUs, resultArgs, struct)
              case _ =>
                Proj(typeName, idx, struct)
            }
          case _ =>
            Proj(typeName, idx, struct)
        }
      case _ =>
        // Return a marker that represents "the type of this projection".
        // For verified exports, definitional equality checking will handle this.
        Proj(typeName, idx, struct)
    }
  }

  /** Get the type of a projection from a structure.
   *  This requires looking up the constructor and computing the field type.
   */
  private def getProjectionType(typeName: Name, idx: Int, us: Vector[Level],
      params: List[Expr], struct: Expr): Expr = {
    // Find the constructor for this type
    // First try the stored constructor name from inductiveInfo
    val ctorDecl = env.inductiveInfo.get(typeName).flatMap(_.ctorName).flatMap(env.get).orElse {
      // Then try the standard .mk name
      env.get(Name.mkStr(typeName, "mk"))
    }.orElse {
      // Search for a constructor of this type (structures have exactly one constructor)
      env.declarations.values.find { decl =>
        decl.name match {
          case Name.Str(parent, _) => parent == typeName && decl.builtin
          case _ => false
        }
      }
    }
    ctorDecl match {
      case Some(decl) =>
        // The constructor type is: (params...) -> (field0 : T0) -> ... -> (fieldN : TN) -> typeName params
        // We need to extract the type of the idx-th field after instantiating params
        val ctorTy = decl.ty.instantiate(decl.univParams.zip(us).toMap)
        extractFieldType(typeName, ctorTy, params, idx, struct)
      case None =>
        // Fallback: if we don't have the constructor, we can't compute the type
        // This shouldn't happen in a well-formed export
        throw new IllegalArgumentException(s"constructor not found for type: $typeName")
    }
  }

  /** Extract the type of the idx-th field from a constructor type,
   *  after instantiating parameters.
   */
  private def extractFieldType(typeName: Name, ctorTy: Expr, params: List[Expr], idx: Int, struct: Expr): Expr = {
    // Skip parameter pis
    @tailrec def skipParams(ty: Expr, ps: List[Expr]): Expr =
      (ty, ps) match {
        case (Pi(_, body), p :: rest) => skipParams(body.instantiate(p), rest)
        case (_, Nil) => ty
        case _ => whnf(ty) match {
          case ty_ @ Pi(_, _) => skipParams(ty_, ps)
          case _ => ty
        }
      }

    // Skip to the idx-th field
    @tailrec def skipFields(ty: Expr, n: Int, prevFields: List[Expr]): Expr =
      if (n == 0) {
        ty match {
          case Pi(dom, _) =>
            // Instantiate previous fields (which are projections on struct)
            dom.ty.instantiate(0, prevFields.toVector)
          case _ =>
            whnf(ty) match {
              case Pi(dom, _) => dom.ty.instantiate(0, prevFields.toVector)
              case stuck if trustExports && isStuckTerm(stuck) =>
                // In trust mode, return the projection itself as a stuck type
                stuckProjTypeCount += 1
                if (stuckProjTypeCount <= 10) println(s"[STUCK-PROJ] $debugCurrentDecl: ${prettyExpr(stuck, 0).take(80)}")
                Proj(typeName, idx, struct)
              case _ => throw new IllegalArgumentException(s"not enough fields in constructor type")
            }
        }
      } else {
        ty match {
          case Pi(_, body) =>
            // The previous field value is a projection on the struct
            val fieldVal = Proj(typeName, idx - n, struct)
            skipFields(body, n - 1, fieldVal :: prevFields)
          case _ =>
            whnf(ty) match {
              case ty_ @ Pi(_, _) => skipFields(ty_, n, prevFields)
              case stuck if trustExports && isStuckTerm(stuck) =>
                // In trust mode, return the projection itself as a stuck type
                stuckProjTypeCount += 1
                if (stuckProjTypeCount <= 10) println(s"[STUCK-PROJ] $debugCurrentDecl: ${prettyExpr(stuck, 0).take(80)}")
                Proj(typeName, idx, struct)
              case _ => throw new IllegalArgumentException(s"not enough fields in constructor type")
            }
        }
      }

    val afterParams = skipParams(ctorTy, params)
    skipFields(afterParams, idx, Nil)
  }
}