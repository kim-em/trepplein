package trepplein

/**
 * Lean 4 kernel extension: literal reduction for Nat and String operations.
 *
 * These implement the built-in operations that Lean 4's kernel can reduce.
 * When the arguments are concrete literals, these operations compute immediately.
 */
object LiteralReduction {

  // Whether to enable literal reductions (can be disabled for debugging)
  var enableNatReduction: Boolean = true
  var enableStringReduction: Boolean = true

  // Helper to match "Nat.xxx" style names
  private val NatName = Name.Str(Name.Anon, "Nat")
  private val StringName = Name.Str(Name.Anon, "String")
  private val BoolName = Name.Str(Name.Anon, "Bool")

  /**
   * Try to reduce an application of a known builtin to literals.
   * Returns Some(result) if reduction is possible, None otherwise.
   */
  def reduceLiteralApp(fn: Expr, args: List[Expr]): Option[Expr] = {
    fn match {
      case Const(name, _) => reduceLiteralConst(name, args)
      case _ => None
    }
  }

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
        reduceNatBinOp(args, (a, b) => a.pow(b.toInt))
      case Name.Str(NatName, "beq") if enableNatReduction =>
        reduceNatCompare(args, _ == _)
      case Name.Str(NatName, "ble") if enableNatReduction =>
        reduceNatCompare(args, _ <= _)
      case Name.Str(NatName, "blt") if enableNatReduction =>
        reduceNatCompare(args, _ < _)
      case Name.Str(NatName, "succ") if enableNatReduction =>
        args match {
          case List(NatLit(n)) => Some(NatLit(n + 1))
          case _ => None
        }

      // String operations
      case Name.Str(StringName, "append") if enableStringReduction =>
        reduceStringBinOp(args, _ + _)
      case Name.Str(StringName, "length") if enableStringReduction =>
        args match {
          case List(StringLit(s)) => Some(NatLit(s.length))
          case _ => None
        }
      case Name.Str(StringName, "push") if enableStringReduction =>
        args match {
          case List(StringLit(s), NatLit(c)) =>
            Some(StringLit(s + c.toChar))
          case _ => None
        }
      case Name.Str(StringName, "beq") if enableStringReduction =>
        reduceStringCompare(args, _ == _)

      case _ => None
    }
  }

  private val boolTrue = Const(Name.Str(BoolName, "true"), Vector())
  private val boolFalse = Const(Name.Str(BoolName, "false"), Vector())

  private def reduceNatBinOp(args: List[Expr], op: (BigInt, BigInt) => BigInt): Option[Expr] = {
    args match {
      case List(NatLit(a), NatLit(b)) => Some(NatLit(op(a, b)))
      case _ => None
    }
  }

  private def reduceNatCompare(args: List[Expr], op: (BigInt, BigInt) => Boolean): Option[Expr] = {
    args match {
      case List(NatLit(a), NatLit(b)) =>
        Some(if (op(a, b)) boolTrue else boolFalse)
      case _ => None
    }
  }

  private def reduceStringBinOp(args: List[Expr], op: (String, String) => String): Option[Expr] = {
    args match {
      case List(StringLit(a), StringLit(b)) => Some(StringLit(op(a, b)))
      case _ => None
    }
  }

  private def reduceStringCompare(args: List[Expr], op: (String, String) => Boolean): Option[Expr] = {
    args match {
      case List(StringLit(a), StringLit(b)) =>
        Some(if (op(a, b)) boolTrue else boolFalse)
      case _ => None
    }
  }
}
