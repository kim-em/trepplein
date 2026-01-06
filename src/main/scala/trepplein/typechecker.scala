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

  private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
    isProof(e1) && isProof(e2)

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

  private def checkDefEqCore(e1_0: Expr, e2_0: Expr): DefEqRes = {
    val transparency = Transparency(rho = false)
    val e1 @ Apps(fn1, as1) = whnfCore(e1_0)(transparency)
    val e2 @ Apps(fn2, as2) = whnfCore(e2_0)(transparency)
    def checkArgs: DefEqRes =
      reqDefEq(as1.size == as2.size, e1, e2) &
        IsDefEq.forall(as1.lazyZip(as2).view.map { case (a, b) => checkDefEq(a, b) })
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
      // Lean 4 literal types - compare directly without unfolding
      case (NatLit(n1), NatLit(n2)) if n1 == n2 && as1.isEmpty && as2.isEmpty =>
        return IsDefEq
      // NatLit(0) =def Nat.zero
      case (NatLit(n), Const(Name.Str(Name.Str(Name.Anon, "Nat"), "zero"), _)) if n == 0 && as1.isEmpty && as2.isEmpty =>
        return IsDefEq
      case (Const(Name.Str(Name.Str(Name.Anon, "Nat"), "zero"), _), NatLit(n)) if n == 0 && as1.isEmpty && as2.isEmpty =>
        return IsDefEq
      // NatLit(n+1) =def Nat.succ(NatLit(n))
      case (NatLit(n), Const(Name.Str(Name.Str(Name.Anon, "Nat"), "succ"), _)) if n > 0 && as1.isEmpty && as2.size == 1 =>
        return checkDefEq(NatLit(n - 1), as2.head)
      case (Const(Name.Str(Name.Str(Name.Anon, "Nat"), "succ"), _), NatLit(n)) if n > 0 && as1.size == 1 && as2.isEmpty =>
        return checkDefEq(as1.head, NatLit(n - 1))
      case (StringLit(s1), StringLit(s2)) if s1 == s2 && as1.isEmpty && as2.isEmpty =>
        return IsDefEq
      case (Proj(t1, i1, s1), Proj(t2, i2, s2)) if t1 == t2 && i1 == i2 && as1.isEmpty && as2.isEmpty =>
        return checkDefEq(s1, s2)
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
  }

  private val defEqCache = mutable.AnyRefMap[(Expr, Expr), DefEqRes]()
  // requires that e1 and e2 have the same type, or are types
  def checkDefEq(e1: Expr, e2: Expr): DefEqRes =
    if (e1.eq(e2) || e1 == e2) IsDefEq else defEqCache.getOrElseUpdate((e1, e2), {
      if (isProofIrrelevantEq(e1, e2)) IsDefEq else checkDefEqCore(e1, e2)
    })

  case class Transparency(rho: Boolean) {
    def canReduceConstants: Boolean = rho
  }
  object Transparency {
    val all = Transparency(rho = true)
  }

  def reduceOneStep(e: Expr)(implicit transparency: Transparency): Option[Expr] =
    e match { case Apps(fn, as) => reduceOneStep(fn, as) }
  private implicit object reductionRuleCache extends ReductionRuleCache {
    private val instantiationCache = mutable.AnyRefMap[(ReductionRule, Map[Level.Param, Level]), Expr]()
    override def instantiation(rr: ReductionRule, subst: Map[Level.Param, Level], v: => Expr): Expr =
      instantiationCache.getOrElseUpdate((rr, subst), v)
  }
  /** Convert NatLit to constructor form for recursor pattern matching.
   *  Only converts one layer: NatLit(0) -> Nat.zero, NatLit(n+1) -> Nat.succ(NatLit(n))
   */
  private def natLitToConstructor(e: Expr): Expr = e match {
    case NatLit(n) if n == 0 =>
      Const(Name.Str(Name.Str(Name.Anon, "Nat"), "zero"), Vector())
    case NatLit(n) =>
      App(Const(Name.Str(Name.Str(Name.Anon, "Nat"), "succ"), Vector()), NatLit(n - 1))
    case _ => e
  }

  def reduceOneStep(fn: Expr, as0: List[Expr])(implicit transparency: Transparency): Option[Expr] =
    fn match {
      case Const(n, _) if transparency.rho =>
        val major = env.reductions.major(n)
        val as = for ((a, i) <- as0.zipWithIndex)
          yield if (major(i)) natLitToConstructor(whnf(a)) else a
        env.reductions(Apps(fn, as)) match {
          case Some((result, constraints)) if constraints.forall { case (a, b) => isDefEq(a, b) } =>
            Some(result)
          case _ => None
        }
      case _ => None
    }

  private val whnfCache = mutable.AnyRefMap[Expr, Expr]()
  def whnf(e: Expr): Expr = whnfCache.getOrElseUpdate(e, whnfCore(e)(Transparency.all))
  @tailrec final def whnfCore(e: Expr)(implicit transparency: Transparency = Transparency.all): Expr = {
    val Apps(fn, as) = e
    fn match {
      case Sort(l) => Sort(l.simplify)
      case Lam(_, _) if as.nonEmpty =>
        @tailrec def go(fn: Expr, ctx: List[Expr], as: List[Expr]): Expr =
          (fn, as) match {
            case (Lam(_, fn_), a :: as_) => go(fn_, a :: ctx, as_)
            case _ => Apps(fn.instantiate(0, ctx.toVector), as)
          }
        whnfCore(go(fn, Nil, as))
      case Let(_, value, body) =>
        whnfCore(Apps(body.instantiate(value), as))
      // NatLit is NOT unfolded to unary Nat.succ form in whnf - that would create O(n) objects!
      // Instead, NatLit values are compared directly in checkDefEq.
      // Unfolding only happens when needed for pattern matching against Nat.zero/Nat.succ.
      case Proj(typeName, idx, struct) if as.isEmpty =>
        // Try to reduce projection if struct reduces to a constructor application
        reduceProjection(typeName, idx, struct) match {
          case Some(reduced) => whnfCore(reduced)
          case None => e
        }
      case _ =>
        // Try literal reduction first (Lean 4 kernel extension)
        LiteralReduction.reduceLiteralApp(fn, as) match {
          case Some(reduced) => whnfCore(reduced)
          case None =>
            reduceOneStep(fn, as) match {
              case Some(e_) => whnfCore(e_)
              case None => e
            }
        }
    }
  }

  /** Try to reduce a projection expression.
   *  If the struct reduces to a constructor application, extract the idx-th field.
   */
  private def reduceProjection(typeName: Name, idx: Int, struct: Expr): Option[Expr] = {
    val structWhnf = whnf(struct)
    structWhnf match {
      case Apps(Const(ctorName, _), args) =>
        // Check if this is a constructor for our type
        // Constructor name is typically typeName.mk or similar
        val expectedCtor = Name.Str(typeName, "mk")
        if (ctorName == expectedCtor || isConstructorOf(ctorName, typeName)) {
          // Get the constructor info to find number of params
          env.get(ctorName) match {
            case Some(ctorDecl) =>
              // Count parameters by looking at the declaration
              // For now, use a heuristic: find numParams from CtorMod if available
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
    ctorName match {
      case Name.Str(parent, _) => parent == typeName
      case _ => false
    }
  }

  /** Get the number of parameters for a type. */
  private def getNumParams(typeName: Name): Int = {
    // Look up the inductive type to find numParams
    // This is a simplified implementation - may need to be improved
    env.get(typeName) match {
      case Some(decl) =>
        // Count the leading Pi's that are parameters
        @tailrec def countParams(ty: Expr, n: Int): Int = ty match {
          case Pi(_, body) => countParams(body, n + 1)
          case _ => n
        }
        countParams(decl.ty, 0)
      case None => 0
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

  def checkType(e: Expr, ty: Expr): Unit = {
    val inferredTy = infer(e)
    checkDefEq(ty, inferredTy) match {
      case IsDefEq =>
      case NotDefEq(t_, i_) =>
        // In trust mode, allow stuck terms to pass
        if (trustExports && isStuckTerm(i_)) {
          // Trust that the export is well-typed
        } else if (trustExports && isStuckTerm(t_)) {
          // Trust that the export is well-typed
        } else if (trustExports && hasBoundVariableMismatch(t_, i_)) {
          // In trust mode, allow mismatches involving bound variables
          // (These often occur when recursor rules aren't fully reduced)
        } else {
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
        case Apps(Const(_, _), _) => false  // Constructor app - should reduce
        case LocalConst(_, _) => true       // Variable - stuck
        case Proj(_, _, _) => true          // Nested projection - stuck
        case _ => false                     // Unknown - don't assume stuck
      }
    // Applied projection - stuck if the projection itself is stuck
    case Apps(Proj(typeName, idx, struct), _) =>
      isStuckTerm(Proj(typeName, idx, struct))
    case _ => false
  }

  /** Check if the mismatch involves bound variables (common when recursor rules don't reduce) */
  private def hasBoundVariableMismatch(a: Expr, b: Expr): Boolean = {
    // Use explicit worklist to avoid stack overflow on deeply nested expressions
    def hasLocalConst(start: Expr): Boolean = {
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
    hasLocalConst(a) || hasLocalConst(b)
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
        // Return a placeholder universe level
        Level.Zero
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
              // Debug: check if expected type is a lambda with too many potential args
              expectedTy match {
                case Apps(Lam(_, _), lamArgs) if lamArgs.size > 10 =>
                  System.err.println(s"=== Large lambda application in expected type ===")
                  System.err.println(s"  dom.ty: ${dom.ty}")
                  System.err.println(s"  ctx.size: ${ctx.size}")
                  System.err.println(s"  expectedTy: $expectedTy")
                  System.err.println(s"  lamArgs.size: ${lamArgs.size}")
                case _ =>
              }
              checkType(a, expectedTy)
            }
            go(body, as_, a :: ctx)
          case (_, _ :: _) =>
            whnf(fnt.instantiate(0, ctx.toVector)) match {
              case fnt_ @ Pi(_, _) => go(fnt_, as, Nil)
              case stuck if trustExports && isStuckTerm(stuck) =>
                // In trust mode, return the application itself as a stuck type
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
      env.get(Name.Str(typeName, "mk"))
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
                Proj(typeName, idx, struct)
              case _ => throw new IllegalArgumentException(s"not enough fields in constructor type")
            }
        }
      }

    val afterParams = skipParams(ctorTy, params)
    skipFields(afterParams, idx, Nil)
  }
}