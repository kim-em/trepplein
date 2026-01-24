package trepplein

/**
 * Lean 4 kernel extension: literal reduction for Nat and String operations.
 *
 * These implement the built-in operations that Lean 4's kernel can reduce.
 * When the arguments are concrete literals, these operations compute immediately.
 *
 * IMPORTANT: This module does NOT call whnf on arguments to avoid infinite
 * recursion with the type checker. It only works on expressions that are
 * ALREADY in literal form. The type checker's whnf loop will reduce arguments
 * through normal reduction rules, and literal reduction will succeed on
 * subsequent iterations when arguments become literals.
 */
object LiteralReduction {

  /** Configuration for literal reduction.
    * To modify these for debugging, change the constants and rebuild.
    */
  object Config {
    /** Enable Nat literal operations (add, sub, mul, div, mod, etc.) */
    val enableNatReduction: Boolean = true
    /** Enable String literal operations (append, length, push, etc.) */
    val enableStringReduction: Boolean = true
    /** Print debug output for HMod reduction */
    val debugHMod: Boolean = false
  }

  import Config._

  // Helper to match "Nat.xxx" style names (use interned names for reference equality)
  private val NatName = Name.mkStr(Name.Anon, "Nat")
  private val StringName = Name.mkStr(Name.Anon, "String")
  private val BoolName = Name.mkStr(Name.Anon, "Bool")
  private val DecidableName = Name.mkStr(Name.Anon, "Decidable")

  /**
   * Try to reduce an application of a known builtin to literals.
   * Returns Some(result) if reduction is possible, None otherwise.
   *
   * IMPORTANT: This does NOT call whnf on arguments - they must already be literals.
   */
  def reduceLiteralApp(fn: Expr, args: List[Expr]): Option[Expr] = {
    fn match {
      case Const(name, _) => reduceLiteralConst(name, args)
      case _ => None
    }
  }

  // Helper to extract a NatLit from an expression
  // Handles NatLit, Nat.zero, Nat.succ chains, OfNat.ofNat for Nat type,
  // and recursively reduces certain typeclass operations (HPow.hPow, etc).
  private def extractNatLit(e: Expr): Option[BigInt] = {
    extractNatLitImpl(e, depth = 0)
  }

  private def extractNatLitImpl(e: Expr, depth: Int): Option[BigInt] = {
    if (depth > 10) return None  // Prevent infinite recursion

    val NatZero = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "zero")
    val NatSucc = Name.mkStr(Name.mkStr(Name.Anon, "Nat"), "succ")
    val OfNatOfNat = Name.mkStr(OfNatName, "ofNat")
    val NatTypeName = Name.mkStr(Name.Anon, "Nat")

    var current = e
    var offset: BigInt = 0
    var maxIter = 100000

    while (maxIter > 0) {
      maxIter -= 1
      current match {
        case NatLit(n) => return Some(n + offset)
        case Const(NatZero, _) => return Some(offset)
        case Apps(Const(NatSucc, _), List(arg)) =>
          offset += 1
          current = arg  // Continue without whnf - just unwrap succ
        // OfNat.ofNat : {α : Type} → (n : Nat) → [inst : OfNat α n] → α
        // Only extract if α = Nat (first arg is Const(Nat) or similar)
        case Apps(Const(OfNatOfNat, _), args) if args.length >= 2 =>
          // Check if first arg (the type) is Nat
          args.head match {
            case Const(NatTypeName, _) => current = args(1)  // Get the Nat argument
            case other =>
              return None  // Not Nat type, don't extract
          }
        // Try to reduce specific typeclass applications that produce Nat
        // Only reduce operations that don't recursively call extractNatLit
        case Apps(Const(name, _), args) =>
          name match {
            // HPow.hPow uses extractNatLit, so we handle it specially here
            // Base can be Nat or Int, exponent is always Nat
            case Name.Str(HPowName, "hPow") =>
              args match {
                case _ :+ a :+ b =>
                  // Try Nat first, then Int for the base
                  val av = extractNatLitImpl(a, depth + 1).orElse(extractIntLit(a))
                  val bv = extractNatLitImpl(b, depth + 1)  // Exponent is always Nat
                  for {
                    avVal <- av
                    bvVal <- bv
                    // Limit exponent to prevent memory exhaustion and ensure bv fits in Int
                    if bvVal >= 0 && bvVal <= 10000
                  } yield {
                    return Some(avVal.pow(bvVal.intValue) + offset)
                  }
                  return None
                case _ => return None
              }
            // HAdd.hAdd, HMul.hMul, etc - only reduce if we can extract both args
            case Name.Str(HAddName, "hAdd") =>
              args match {
                case _ :+ a :+ b =>
                  for {
                    av <- extractNatLitImpl(a, depth + 1)
                    bv <- extractNatLitImpl(b, depth + 1)
                  } yield {
                    return Some(av + bv + offset)
                  }
                  return None
                case _ => return None
              }
            case Name.Str(HMulName, "hMul") =>
              args match {
                case _ :+ a :+ b =>
                  for {
                    av <- extractNatLitImpl(a, depth + 1)
                    bv <- extractNatLitImpl(b, depth + 1)
                  } yield {
                    return Some(av * bv + offset)
                  }
                  return None
                case _ => return None
              }
            case Name.Str(HSubName, "hSub") =>
              args match {
                case _ :+ a :+ b =>
                  for {
                    av <- extractNatLitImpl(a, depth + 1)
                    bv <- extractNatLitImpl(b, depth + 1)
                  } yield {
                    return Some((av - bv).max(0) + offset)
                  }
                  return None
                case _ => return None
              }
            case Name.Str(HModName, "hMod") =>
              args match {
                case _ :+ a :+ b =>
                  for {
                    av <- extractNatLitImpl(a, depth + 1)
                    bv <- extractNatLitImpl(b, depth + 1)
                  } yield {
                    return Some((if (bv == 0) av else av % bv) + offset)
                  }
                  return None
                case _ => return None
              }
            case Name.Str(HDivName, "hDiv") =>
              args match {
                case _ :+ a :+ b =>
                  for {
                    av <- extractNatLitImpl(a, depth + 1)
                    bv <- extractNatLitImpl(b, depth + 1)
                  } yield {
                    return Some((if (bv == 0) BigInt(0) else av / bv) + offset)
                  }
                  return None
                case _ => return None
              }
            case _ => return None
          }
        case _ => return None
      }
    }
    None
  }

  // Helper to extract a StringLit from an expression
  // Only checks if expression is already a literal - no reduction!
  private def extractStringLit(e: Expr): Option[String] = {
    e match {
      case StringLit(s) => Some(s)
      case _ => None
    }
  }

  // Helper to extract a Decidable constructor
  // Returns Left(proof) for isFalse, Right(proof) for isTrue
  private def extractDecidable(e: Expr): Option[Either[Expr, Expr]] = {
    val IsTrue = Name.mkStr(DecidableName, "isTrue")
    val IsFalse = Name.mkStr(DecidableName, "isFalse")

    e match {
      case Apps(Const(IsTrue, _), args) =>
        // Decidable.isTrue : {P : Prop} → P → Decidable P
        // Last arg is the proof
        args.lastOption.map(Right(_))
      case Apps(Const(IsFalse, _), args) =>
        // Decidable.isFalse : {P : Prop} → ¬P → Decidable P
        // Last arg is the proof
        args.lastOption.map(Left(_))
      case _ => None
    }
  }

  // Helper to extract an Int value from an expression
  // Handles Int.ofNat NatLit(n) and Int.negSucc NatLit(n)
  private val IntOfNat = Name.mkStr(Name.mkStr(Name.Anon, "Int"), "ofNat")
  private val IntNegSucc = Name.mkStr(Name.mkStr(Name.Anon, "Int"), "negSucc")

  private val IntTypeName = Name.mkStr(Name.Anon, "Int")
  private val OfNatOfNatName = Name.mkStr(OfNatName, "ofNat")

  private def extractIntLit(e: Expr): Option[BigInt] = {
    e match {
      case NatLit(n) => Some(n)  // NatLit can be viewed as non-negative Int
      case Apps(Const(name, _), List(arg)) if name == IntOfNat =>
        extractNatLit(arg)
      case Apps(Const(name, _), List(arg)) if name == IntNegSucc =>
        extractNatLit(arg).map(n => -(n + 1))
      // OfNat.ofNat : {α : Type} → (n : Nat) → [inst : OfNat α n] → α
      // Handle OfNat.ofNat for Int type
      case Apps(Const(name, _), args) if name == OfNatOfNatName && args.length >= 2 =>
        args.head match {
          case Const(IntTypeName, _) => extractNatLit(args(1))  // Get the Nat argument
          case _ => None
        }
      case _ => None
    }
  }

  // Convert BigInt to Int expression
  private def mkIntLit(n: BigInt): Expr = {
    if (n >= 0) {
      App(Const(IntOfNat, Vector()), NatLit(n))
    } else {
      App(Const(IntNegSucc, Vector()), NatLit(-(n + 1)))
    }
  }

  // Additional type names for typeclass operations (use interned names)
  private val HModName = Name.mkStr(Name.Anon, "HMod")
  private val HAddName = Name.mkStr(Name.Anon, "HAdd")
  private val HSubName = Name.mkStr(Name.Anon, "HSub")
  private val HMulName = Name.mkStr(Name.Anon, "HMul")
  private val HDivName = Name.mkStr(Name.Anon, "HDiv")
  private val HPowName = Name.mkStr(Name.Anon, "HPow")
  private val NegName = Name.mkStr(Name.Anon, "Neg")
  private val OfNatName = Name.mkStr(Name.Anon, "OfNat")
  private val BEqName = Name.mkStr(Name.Anon, "BEq")

  private def reduceLiteralConst(name: Name, args: List[Expr]): Option[Expr] = {
    name match {
      // Nat operations
      case Name.Str(NatName, "add") if enableNatReduction =>
        reduceNatBinOp(args, _ + _)
      case Name.Str(NatName, "sub") if enableNatReduction =>
        reduceNatBinOp(args, (a, b) => (a - b).max(0))
      case Name.Str(NatName, "mul") if enableNatReduction =>
        reduceNatBinOp(args, _ * _)
      case Name.Str(NatName, "div") if enableNatReduction =>
        reduceNatBinOp(args, (a, b) => if (b == 0) BigInt(0) else a / b)
      case Name.Str(NatName, "mod") if enableNatReduction =>
        reduceNatBinOp(args, (a, b) => if (b == 0) a else a % b)
      case Name.Str(NatName, "pow") if enableNatReduction =>
        args match {
          case List(a, b) =>
            for {
              av <- extractNatLit(a)
              bv <- extractNatLit(b)
              // Limit exponent to prevent memory exhaustion and ensure bv fits in Int
              if bv >= 0 && bv <= 10000
            } yield NatLit(av.pow(bv.intValue))
          case _ => None
        }
      case Name.Str(NatName, "beq") if enableNatReduction =>
        reduceNatCompare(args, _ == _)
      case Name.Str(NatName, "ble") if enableNatReduction =>
        reduceNatCompare(args, _ <= _)
      case Name.Str(NatName, "blt") if enableNatReduction =>
        reduceNatCompare(args, _ < _)
      case Name.Str(NatName, "succ") if enableNatReduction =>
        args match {
          case List(a) =>
            extractNatLit(a).map(n => NatLit(n + 1))
          case _ => None
        }

      // Nat.casesOn - pattern match on Nat literal without unfolding
      // Nat.casesOn.{u} : {motive : Nat → Sort u} → (n : Nat) → motive Nat.zero → ((n : Nat) → motive (Nat.succ n)) → motive n
      // Note: Only checks if n is already a literal - doesn't call whnf to avoid cycles
      // May have extra args for instantiation of the motive
      case Name.Str(NatName, "casesOn") if enableNatReduction =>
        args match {
          case motive :: n :: zeroCase :: succCase :: extraArgs =>
            extractNatLit(n).map { nv =>
              val result = if (nv == 0) zeroCase else App(succCase, NatLit(nv - 1))
              Apps(result, extraArgs)
            }
          case _ => None
        }

      // Decidable.casesOn - reduce when the decidable instance is a constructor
      // Decidable.casesOn : {P : Prop} → {motive : Decidable P → Sort u} →
      //   (t : Decidable P) → ((h : ¬P) → motive (isFalse h)) → ((h : P) → motive (isTrue h)) → motive t
      case Name.Str(DecidableName, "casesOn") =>
        args match {
          case _ :: _ :: t :: falseCase :: trueCase :: extraArgs =>
            extractDecidable(t).map {
              case Left(h) => Apps(App(falseCase, h), extraArgs)
              case Right(h) => Apps(App(trueCase, h), extraArgs)
            }
          case _ => None
        }

      // Decidable.rec - reduce when the decidable instance is a constructor
      // Decidable.rec : {P : Prop} → {motive : Decidable P → Sort u} →
      //   ((h : ¬P) → motive (isFalse h)) → ((h : P) → motive (isTrue h)) → (t : Decidable P) → motive t
      case Name.Str(DecidableName, "rec") =>
        args match {
          case _ :: _ :: falseCase :: trueCase :: t :: extraArgs =>
            extractDecidable(t).map {
              case Left(h) => Apps(App(falseCase, h), extraArgs)
              case Right(h) => Apps(App(trueCase, h), extraArgs)
            }
          case _ => None
        }

      // Decidable.decide - convert Decidable to Bool
      // Decidable.decide : (p : Prop) → [d : Decidable p] → Bool
      case Name.Str(DecidableName, "decide") =>
        args match {
          case _ :: d :: Nil =>
            // First try to extract directly
            extractDecidable(d).map {
              case Left(_) => boolFalse
              case Right(_) => boolTrue
            }.orElse {
              // If d is not a constructor, try to reduce it first
              d match {
                case Apps(Const(instName, _), instArgs) =>
                  reduceLiteralConst(instName, instArgs).flatMap { reduced =>
                    extractDecidable(reduced).map {
                      case Left(_) => boolFalse
                      case Right(_) => boolTrue
                    }
                  }
                case _ => None
              }
            }
          case _ => None
        }

      // String operations
      case Name.Str(StringName, "append") if enableStringReduction =>
        reduceStringBinOp(args, _ + _)
      case Name.Str(StringName, "length") if enableStringReduction =>
        args match {
          case List(s) =>
            extractStringLit(s).map(str => NatLit(str.length))
          case _ => None
        }
      case Name.Str(StringName, "push") if enableStringReduction =>
        args match {
          case List(s, c) =>
            for {
              sv <- extractStringLit(s)
              cv <- extractNatLit(c)
            } yield StringLit(sv + cv.toChar)
          case _ => None
        }
      case Name.Str(StringName, "beq") if enableStringReduction =>
        reduceStringCompare(args, _ == _)

      // Typeclass operations - try Nat first, then Int
      case Name.Str(HModName, "hMod") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>  // Match last two args
            val av = extractNatLit(a)
            val bv = extractNatLit(b)
            if (debugHMod && (av.isDefined || bv.isDefined)) {
              println(s"[HMOD] a = ${a.toString.take(150)}, av = $av")
              println(s"[HMOD] b = ${b.toString.take(150)}, bv = $bv")
            }
            reduceNatBinOp(List(a, b), (x, y) => if (y == 0) x else x % y)
              .orElse(reduceIntBinOp(List(a, b), (x, y) => if (y == 0) x else x % y))
          case _ => None
        }
      case Name.Str(HAddName, "hAdd") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>
            reduceNatBinOp(List(a, b), _ + _)
              .orElse(reduceIntBinOp(List(a, b), _ + _))
          case _ => None
        }
      case Name.Str(HSubName, "hSub") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>
            reduceNatBinOp(List(a, b), (x, y) => (x - y).max(0))
              .orElse(reduceIntBinOp(List(a, b), _ - _))
          case _ => None
        }
      case Name.Str(HMulName, "hMul") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>
            reduceNatBinOp(List(a, b), _ * _)
              .orElse(reduceIntBinOp(List(a, b), _ * _))
          case _ => None
        }
      case Name.Str(HDivName, "hDiv") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>
            reduceNatBinOp(List(a, b), (x, y) => if (y == 0) BigInt(0) else x / y)
              .orElse(reduceIntBinOp(List(a, b), (x, y) => if (y == 0) BigInt(0) else x / y))
          case _ => None
        }
      case Name.Str(HPowName, "hPow") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>
            // Try extracting as Nat first, then Int
            val av = extractNatLit(a).orElse(extractIntLit(a))
            val bv = extractNatLit(b)  // Exponent is always Nat
            for {
              avVal <- av
              bvVal <- bv
              // Limit exponent to prevent memory exhaustion and ensure bv fits in Int
              if bvVal >= 0 && bvVal <= 10000
            } yield NatLit(avVal.pow(bvVal.intValue))
          case _ => None
        }

      // Neg.neg : {α : Type} → [inst : Neg α] → α → α
      // For Int literals: negate the value
      case Name.Str(NegName, "neg") if enableNatReduction =>
        args match {
          case _ :+ a =>  // Last arg is the value to negate
            extractIntLit(a).map(n => mkIntLit(-n))
          case _ => None
        }

      // NOTE: OfNat.ofNat is NOT handled here because it's type-polymorphic.
      // For Nat it should return the literal, for Int it should return Int.ofNat.
      // Let the normal reduction rules unfold OfNat.ofNat to the instance's method.

      // BEq.beq : {α : Type} → [inst : BEq α] → α → α → Bool
      case Name.Str(BEqName, "beq") if enableNatReduction =>
        args match {
          case _ :+ a :+ b =>
            reduceNatCompare(List(a, b), _ == _)
              .orElse(reduceIntCompare(List(a, b), _ == _))
          case _ => None
        }

      // NOTE: Nat.decEq, Nat.decLe, Nat.decLt are NOT reduced here.
      // Following nanoda_lib's approach, we don't reduce decidability instances
      // because we can't produce proper proof terms. See PLAN.md.
      // We DO reduce Nat.beq/Nat.ble to Bool values above.

      case _ => None
    }
  }

  private val boolTrue = Const(Name.mkStr(BoolName, "true"), Vector())
  private val boolFalse = Const(Name.mkStr(BoolName, "false"), Vector())

  private def reduceNatBinOp(args: List[Expr], op: (BigInt, BigInt) => BigInt): Option[Expr] = {
    args match {
      case List(a, b) =>
        for {
          av <- extractNatLit(a)
          bv <- extractNatLit(b)
        } yield NatLit(op(av, bv))
      case _ => None
    }
  }

  private def reduceNatCompare(args: List[Expr], op: (BigInt, BigInt) => Boolean): Option[Expr] = {
    args match {
      case List(a, b) =>
        for {
          av <- extractNatLit(a)
          bv <- extractNatLit(b)
        } yield (if (op(av, bv)) boolTrue else boolFalse)
      case _ => None
    }
  }

  private def reduceIntBinOp(args: List[Expr], op: (BigInt, BigInt) => BigInt): Option[Expr] = {
    args match {
      case List(a, b) =>
        for {
          av <- extractIntLit(a)
          bv <- extractIntLit(b)
        } yield mkIntLit(op(av, bv))
      case _ => None
    }
  }

  private def reduceIntCompare(args: List[Expr], op: (BigInt, BigInt) => Boolean): Option[Expr] = {
    args match {
      case List(a, b) =>
        for {
          av <- extractIntLit(a)
          bv <- extractIntLit(b)
        } yield (if (op(av, bv)) boolTrue else boolFalse)
      case _ => None
    }
  }

  private def reduceStringBinOp(args: List[Expr], op: (String, String) => String): Option[Expr] = {
    args match {
      case List(a, b) =>
        for {
          av <- extractStringLit(a)
          bv <- extractStringLit(b)
        } yield StringLit(op(av, bv))
      case _ => None
    }
  }

  private def reduceStringCompare(args: List[Expr], op: (String, String) => Boolean): Option[Expr] = {
    args match {
      case List(a, b) =>
        for {
          av <- extractStringLit(a)
          bv <- extractStringLit(b)
        } yield (if (op(av, bv)) boolTrue else boolFalse)
      case _ => None
    }
  }
}
