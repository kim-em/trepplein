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
    def check(): Unit = {
      decl.check(env)
      // Note: We don't check that declared universe params appear in the type.
      // Some valid inductives have params only in constructors (e.g., Lean.ToLevel.{u}
      // has type `Type` but its constructor takes `α : Type u`).
      // The Lean 4 kernel, lean4lean, and nanoda all skip this check.
      // Constructor types come via separate #CTOR declarations, so we can't easily
      // check them here anyway.
    }
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq()
  }
}

/** Check that an inductive type only appears in strictly positive positions in constructor types.
  *
  * A type T occurs strictly positively in an expression E if:
  * - T doesn't occur in E, or
  * - E = T applied to arguments (the recursive case), or
  * - E = (x : A) -> B where T doesn't occur in A, and occurs strictly positively in B
  *
  * The key insight is that T appearing on the left of an arrow (in a negative position) is disallowed.
  * For nested occurrences like `List T`, we assume the outer type is strictly positive in its arguments
  * (which is true for well-formed inductive types in the environment).
  *
  * We DO check inside type applications for negative occurrences, e.g., `List (T → X)` is rejected
  * because T appears on the left of an arrow inside the type argument.
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

  // Check for negative occurrences in an expression (T appearing on left side of arrows).
  // This is called recursively on type arguments to catch cases like `List (T → X)`.
  def hasNegativeOccurrence(e: Expr): Boolean = e match {
    case Pi(Binding(_, dom, _), body) =>
      // T on left of arrow is negative
      occursIn(dom, indName) || hasNegativeOccurrence(body)
    case App(fn, arg) =>
      // Check inside type applications recursively
      hasNegativeOccurrence(fn) || hasNegativeOccurrence(arg)
    case Lam(Binding(_, dom, _), body) =>
      hasNegativeOccurrence(dom) || hasNegativeOccurrence(body)
    case Let(Binding(_, ty, _), value, body) =>
      hasNegativeOccurrence(ty) || hasNegativeOccurrence(value) || hasNegativeOccurrence(body)
    case Proj(_, _, struct) =>
      hasNegativeOccurrence(struct)
    case _ => false
  }

  // Check that indName occurs only in strictly positive positions.
  // isArgType indicates we're checking an argument type (not the constructor body)
  def checkPositive(ty: Expr, isArgType: Boolean): Unit = ty match {
    case Pi(Binding(_, dom, _), body) =>
      if (isArgType) {
        // Inside an argument type, T cannot appear on the left of any arrow
        // This catches direct cases like `(T → X) → Y`
        if (occursIn(dom, indName)) {
          throw new IllegalArgumentException(
            s"inductive type $indName has non-positive occurrence in constructor type")
        }
        // Also check for negative occurrences in the body
        checkPositive(body, isArgType = true)
      } else {
        // At the top level of constructor type, check positivity in arg type
        checkPositive(dom, isArgType = true)
        checkPositive(body, isArgType = false)
      }
    case _ =>
      // Not a Pi type. If we're in an argument type, check for negative occurrences
      // inside the type expression (e.g., `List (T → X)` has T in negative position inside)
      if (isArgType && hasNegativeOccurrence(ty)) {
        throw new IllegalArgumentException(
          s"inductive type $indName has non-positive occurrence inside type argument")
      }
  }

  val bodyTy = skipParams(ctorTy, numParams)
  checkPositive(bodyTy, isArgType = false)
}
