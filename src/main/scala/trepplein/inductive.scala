package trepplein

/**
 * Lean 4 inductive type handling.
 *
 * In Lean 4, constructors and recursors are declared explicitly in the export:
 * - #IND: declares the inductive type itself
 * - #CTOR: declares each constructor (handled by CtorMod in environment.scala)
 * - #REC: declares the recursor with reduction rules (handled by RecursorMod in environment.scala)
 *
 * This is much simpler than Lean 3 where trepplein had to generate recursors.
 */

/** Inductive type modification - just registers the type declaration */
final case class IndMod(name: Name, univParams: Vector[Level.Param], ty: Expr,
    numParams: Int, intros: Vector[(Name, Expr)]) extends Modification {

  val decl = Declaration(name, univParams, ty, builtin = true)

  def compile(env: PreEnvironment) = new CompiledModification {
    def check(): Unit = decl.check(env)
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq()
  }
}

/** Check that an inductive type only appears in strictly positive positions in constructor types.
  *
  * A type T occurs strictly positively in an expression E if:
  * - T doesn't occur in E, or
  * - E = T applied to arguments, or
  * - E = (x : A) -> B where T occurs strictly positively in BOTH A and B
  *
  * The key insight is that T appearing as a direct argument (like `xs : List A`) is allowed,
  * but T appearing on the left of an arrow in an argument type (like `f : (List A → X)`) is not.
  */
def checkStrictPositivity(indName: Name, ctorTy: Expr, numParams: Int): Unit = {
  // Skip the parameters in the constructor type
  def skipParams(ty: Expr, n: Int): Expr = {
    if (n <= 0) ty
    else ty match {
      case Pi(_, body) => skipParams(body, n - 1)
      case _ => ty
    }
  }

  // Check if a name occurs anywhere in an expression
  def occursIn(e: Expr, target: Name): Boolean = e match {
    case Const(n, _) => n == target
    case App(fn, arg) => occursIn(fn, target) || occursIn(arg, target)
    case Lam(Binding(_, dom, _), body) => occursIn(dom, target) || occursIn(body, target)
    case Pi(Binding(_, dom, _), body) => occursIn(dom, target) || occursIn(body, target)
    case Let(Binding(_, ty, _), value, body) =>
      occursIn(ty, target) || occursIn(value, target) || occursIn(body, target)
    case Proj(_, _, struct) => occursIn(struct, target)
    case _ => false
  }

  // Check that indName occurs only in strictly positive positions.
  // isArgType indicates we're checking an argument type (not the constructor body)
  def checkPositive(ty: Expr, isArgType: Boolean): Unit = ty match {
    case Pi(Binding(_, dom, _), body) =>
      if (isArgType) {
        // Inside an argument type, T cannot appear on the left of any arrow
        // This catches cases like `(T → X) → Y` where T is in negative position
        if (occursIn(dom, indName)) {
          throw new IllegalArgumentException(
            s"inductive type $indName has non-positive occurrence in constructor type")
        }
        checkPositive(body, isArgType = true)
      } else {
        // At the top level of constructor type, check that T is strictly positive in arg types
        // T can appear in dom (like `xs : List A`) but must be strictly positive there
        checkPositive(dom, isArgType = true)
        checkPositive(body, isArgType = false)
      }
    case _ =>
      // Not a Pi type - return type at this level, indName can appear freely
      ()
  }

  val bodyTy = skipParams(ctorTy, numParams)
  checkPositive(bodyTy, isArgType = false)
}
