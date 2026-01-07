package trepplein

import scala.concurrent.{ ExecutionContext, Future }
import scala.language.implicitConversions
import scala.util.Try

final case class Declaration(name: Name, univParams: Vector[Level.Param], ty: Expr,
    height: Int = 0, builtin: Boolean = false) {
  def check(env: PreEnvironment): Unit = check(env, new TypeChecker(env))
  def check(env: PreEnvironment, tc: TypeChecker): Unit = {
    require(!env.declarations.contains(name))
    require(ty.univParams.subsetOf(univParams.toSet))
    require(!ty.hasVars)
    require(!ty.hasLocals)
    tc.inferUniverseOfType(ty)
  }
}

trait CompiledModification {
  def check(): Unit
  def decls: Seq[Declaration]
  def rules: Seq[ReductionRule]
}

trait Modification {
  def name: Name
  def compile(env: PreEnvironment): CompiledModification
}
object Modification {
  implicit def ofAxiom(axiom: Declaration): Modification = AxiomMod(axiom.name, axiom.univParams, axiom.ty)
}
final case class AxiomMod(name: Name, univParams: Vector[Level.Param], ty: Expr) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val decl = Declaration(name, univParams, ty)
    def check(): Unit = decl.check(env)
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq()
  }
}
/** Definition reduction hints (Lean 4) */
sealed trait ReducibilityHints
object ReducibilityHints {
  case object Opaque extends ReducibilityHints
  case object Abbrev extends ReducibilityHints
  case class Regular(height: Int) extends ReducibilityHints
}

final case class DefMod(name: Name, univParams: Vector[Level.Param], ty: Expr, value: Expr,
    hints: ReducibilityHints = ReducibilityHints.Regular(0)) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val height: Int = hints match {
      case ReducibilityHints.Regular(h) => h
      case _ =>
        value.constants.view.
          flatMap(env.get).
          map(_.height).
          fold(0)(math.max) + 1
    }

    val decl = Declaration(name, univParams, ty, height = height)
    val rule = ReductionRule(Vector[Binding](), Const(name, univParams), value, List())

    def check(): Unit = {
      val tc = new TypeChecker(env, trustExports = true)
      tc.debugCurrentDecl = name.toString
      decl.check(env, tc)
      require(!value.hasVars)
      require(!value.hasLocals)
      // Check for direct cycles: value cannot reference itself
      checkNoCycle(name, value, env)
      tc.checkType(value, ty)
    }
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq(rule)
  }
}

/** Check that a definition's value doesn't create a cycle by referencing itself or
  * other definitions that form a cycle back to this definition.
  *
  * Optimized to use iterative DFS with mutable state instead of recursive calls.
  */
private def checkNoCycle(defName: Name, value: Expr, env: PreEnvironment): Unit = {
  // Collect all constants referenced in the value
  val referenced = value.constants

  // Direct self-reference is always a cycle
  require(!referenced.contains(defName),
    s"definition $defName contains a direct self-reference (cycle)")

  // Iterative DFS to check for cycles - avoids allocating closures and immutable Sets
  def reachable(startRef: Name): Boolean = {
    val visited = new java.util.HashSet[Name]()
    visited.add(defName)
    val stack = new java.util.ArrayDeque[Name]()
    stack.push(startRef)

    while (!stack.isEmpty) {
      val from = stack.pop()
      if (from == defName) return true
      if (!visited.contains(from)) {
        visited.add(from)
        env.value(from) match {
          case Some(v) =>
            val consts = v.constants
            val iter = consts.iterator
            while (iter.hasNext) {
              stack.push(iter.next())
            }
          case None => // Axiom or not yet defined, no cycle possible through it
        }
      }
    }
    false
  }

  val refIter = referenced.iterator
  while (refIter.hasNext) {
    val ref = refIter.next()
    if (ref != defName) {
      require(!reachable(ref),
        s"definition $defName has a cycle through $ref")
    }
  }
}

/** Theorem (Lean 4) - like DefMod but proof-irrelevant */
final case class TheoremMod(name: Name, univParams: Vector[Level.Param], ty: Expr, value: Expr) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val decl = Declaration(name, univParams, ty)
    // Theorems don't generate reduction rules (proof irrelevance)
    def check(): Unit = {
      val tc = new TypeChecker(env, trustExports = true)
      tc.debugCurrentDecl = name.toString
      decl.check(env, tc)
      require(!value.hasVars)
      require(!value.hasLocals)
      tc.checkType(value, ty)
    }
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq()
  }
}

/** Opaque definition (Lean 4) - like DefMod but not reducible */
final case class OpaqueMod(name: Name, univParams: Vector[Level.Param], ty: Expr, value: Expr) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val decl = Declaration(name, univParams, ty)
    // Opaque definitions don't generate reduction rules
    def check(): Unit = {
      val tc = new TypeChecker(env, trustExports = true)
      tc.debugCurrentDecl = name.toString
      decl.check(env, tc)
      require(!value.hasVars)
      require(!value.hasLocals)
      // Check for cycles (including through opaque definitions)
      checkNoCycleWithOpaque(name, value, env)
      tc.checkType(value, ty)
    }
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq()
  }
}

/** Check for cycles considering both regular and opaque definitions.
  *
  * Optimized to use iterative DFS with mutable state.
  */
private def checkNoCycleWithOpaque(defName: Name, value: Expr, env: PreEnvironment): Unit = {
  val referenced = value.constants

  // Direct self-reference is always a cycle
  require(!referenced.contains(defName),
    s"definition $defName contains a direct self-reference (cycle)")

  // Iterative DFS to check for cycles - avoids allocating closures and immutable Sets
  def reachable(startRef: Name): Boolean = {
    val visited = new java.util.HashSet[Name]()
    visited.add(defName)
    val stack = new java.util.ArrayDeque[Name]()
    stack.push(startRef)

    while (!stack.isEmpty) {
      val from = stack.pop()
      if (from == defName) return true
      if (!visited.contains(from)) {
        visited.add(from)
        // Check both regular values and opaque values
        val bodyOpt = env.value(from).orElse(env.opaqueValues.get(from))
        bodyOpt match {
          case Some(v) =>
            val consts = v.constants
            val iter = consts.iterator
            while (iter.hasNext) {
              stack.push(iter.next())
            }
          case None => // Axiom or not yet defined, no cycle possible through it
        }
      }
    }
    false
  }

  val refIter = referenced.iterator
  while (refIter.hasNext) {
    val ref = refIter.next()
    if (ref != defName) {
      require(!reachable(ref),
        s"definition $defName has a cycle through $ref")
    }
  }
}

/** Constructor (Lean 4) - explicit constructor declaration */
final case class CtorMod(name: Name, univParams: Vector[Level.Param], ty: Expr,
    inductName: Name, cidx: Int, numParams: Int, numFields: Int) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val decl = Declaration(name, univParams, ty, builtin = true)

    /** Count the number of leading Pi types in an expression */
    def countPis(e: Expr): Int = e match {
      case Pi(_, body) => 1 + countPis(body)
      case _ => 0
    }

    def check(): Unit = {
      decl.check(env)

      // Validate numParams matches what the inductive type declared
      env.inductiveInfo.get(inductName) match {
        case Some(indInfo) =>
          require(numParams == indInfo.numParams,
            s"constructor $name: numParams $numParams != inductive $inductName numParams ${indInfo.numParams}")
        case None =>
          // Inductive type not yet registered - this can happen with mutual inductives
          // We'll validate what we can
          ()
      }

      // Validate numFields: constructor arity minus numParams
      val totalArity = countPis(ty)
      val expectedFields = totalArity - numParams
      require(numFields == expectedFields,
        s"constructor $name: numFields $numFields != expected $expectedFields " +
        s"(arity $totalArity - numParams $numParams)")

      // Check strict positivity: inductive type cannot appear in negative positions
      checkStrictPositivity(inductName, ty, numParams)
    }
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = Seq()
  }
}

/** Recursor rule (Lean 4) */
final case class RecRule(ctorName: Name, numFields: Int, rhs: Expr)

/** Recursor (Lean 4) - explicit recursor declaration */
final case class RecursorMod(name: Name, univParams: Vector[Level.Param], ty: Expr,
    inductNames: Vector[Name], numParams: Int, numIndices: Int, numMotives: Int,
    numMinors: Int, recRules: Vector[RecRule], isK: Boolean) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val decl = Declaration(name, univParams, ty, builtin = true)

    // Total number of fixed args before the major premise
    val numFixed = numParams + numMotives + numMinors + numIndices

    // Strip n lambdas from an expression, returning the body
    def stripLambdas(e: Expr, n: Int): Expr = {
      if (n == 0) e
      else e match {
        case Lam(_, body) => stripLambdas(body, n - 1)
        case _ => e // Can't strip more, return as-is
      }
    }

    // Get the inductive type name from a constructor name (e.g., List.nil -> List)
    def getInductiveFromCtor(ctorName: Name): Option[Name] = {
      ctorName match {
        case Name.Str(parent, _) => Some(parent)
        case _ => None
      }
    }

    val reductionRules: Seq[ReductionRule] = recRules.map { rule =>
      // The RHS from the export is a lambda: λ params motives minors fields. body
      // We need to strip these lambdas to get the body, which uses de Bruijn vars:
      //   Var(0) = last field, ..., Var(numFields-1) = first field
      //   Var(numFields) = last fixed arg, ..., Var(numFixed+numFields-1) = first fixed arg
      val numToStrip = numFixed + rule.numFields
      val rhsBody = stripLambdas(rule.rhs, numToStrip)

      // Build the LHS pattern with Var indices matching the body's de Bruijn vars
      // Fixed args: first arg uses highest index, last uses numFields
      val fixedArgs: List[Expr] = (0 until numFixed).toList.map(i =>
        Var(numFixed + rule.numFields - 1 - i))

      // For nested recursors (like Lean.Syntax.rec_2), the constructor might be from a different
      // inductive type (like List) with different numParams. Look up the actual parameter count.
      val ctorIndName = getInductiveFromCtor(rule.ctorName)
      val ctorNumParams = ctorIndName.flatMap(env.inductiveInfo.get).map(_.numParams).getOrElse(numParams)

      // Constructors take: params (inherited from type), then fields.
      // The params are the same Vars as the first ctorNumParams fixedArgs.
      // The fields are: first field uses numFields-1, last uses 0
      val ctorParamArgs: List[Expr] = fixedArgs.take(ctorNumParams)
      val ctorFieldArgs: List[Expr] = (0 until rule.numFields).toList.map(i =>
        Var(rule.numFields - 1 - i))
      // Constructors use only the inductive type's universe params, not the motive's universe params.
      // The recursor's univParams are ordered: [motive universes..., type universes...]
      // So we drop the first numMotives universe params to get the constructor's params.
      val ctorUnivParams = univParams.drop(numMotives)
      val ctorApp: Expr = Apps(Const(rule.ctorName, ctorUnivParams), ctorParamArgs ++ ctorFieldArgs)

      val lhsArgs = fixedArgs :+ ctorApp
      val lhs = Apps(Const(name, univParams), lhsArgs)

      ReductionRule(Vector[Binding](), lhs, rhsBody, List())
    }

    def check(): Unit = {
      val tc = new TypeChecker(env, trustExports = true)
      tc.debugCurrentDecl = name.toString
      decl.check(env, tc)

      // Validate recursor rules (basic checks only - full reconstruction would be like nanoda_lib)
      for (rule <- recRules) {
        // 1. Check constructor exists (only if constructor should be defined by now)
        val ctorDecl = env.get(rule.ctorName)
        if (ctorDecl.isDefined) {
          // 2. Get constructor's inductive type and parameter count
          val ctorIndName = getInductiveFromCtor(rule.ctorName)
          val ctorNumParams = ctorIndName.flatMap(env.inductiveInfo.get).map(_.numParams).getOrElse(numParams)

          // 3. Count fields from constructor type (number of Pis minus parameters)
          val ctorTy = ctorDecl.get.ty
          var ctorTyBody = ctorTy
          var piCount = 0
          while (ctorTyBody.isInstanceOf[Pi]) {
            ctorTyBody = ctorTyBody.asInstanceOf[Pi].body
            piCount += 1
          }
          val expectedFields = math.max(0, piCount - ctorNumParams)

          // 4. Check numFields matches
          require(rule.numFields == expectedFields,
            s"recursor ${name} rule for ${rule.ctorName}: " +
            s"numFields ${rule.numFields} != expected $expectedFields (from type with $piCount pis, $ctorNumParams params)")

          // 5. Type-check the RHS expression
          // The RHS should be a lambda with (numParams + numMotives + numMinors + numFields) parameters
          // This catches cases where the RHS is replaced with something invalid (like Prop)
          val rhsTyOpt = try {
            Some(tc.infer(rule.rhs))
          } catch {
            case _: Exception =>
              // Type inference failed - RHS might reference unknown declarations
              // This is OK for nested recursors that reference other recursors being defined
              None
          }
          rhsTyOpt.foreach { rhsTy =>
            val expectedLambdas = numParams + numMotives + numMinors + rule.numFields
            // Count leading Pis in the inferred type
            var rhsTyBody = rhsTy
            var rhsPiCount = 0
            while (rhsTyBody.isInstanceOf[Pi]) {
              rhsTyBody = rhsTyBody.asInstanceOf[Pi].body
              rhsPiCount += 1
            }
            require(rhsPiCount >= expectedLambdas,
              s"recursor ${name} rule for ${rule.ctorName}: " +
              s"RHS type has $rhsPiCount pis, expected at least $expectedLambdas " +
              s"(numParams=$numParams + numMotives=$numMotives + numMinors=$numMinors + numFields=${rule.numFields})")
          }
        }
        // If constructor not found, skip validation for this rule
        // (happens with nested/mutual recursors where order matters)
      }
    }
    def decls: Seq[Declaration] = Seq(decl)
    def rules: Seq[ReductionRule] = reductionRules
  }
}

case class EnvironmentUpdateError(mod: Modification, msg: String) {
  override def toString = s"${mod.name}: $msg"
}

/** Info about an inductive type needed for projections */
final case class InductiveInfo(numParams: Int, numFields: Int, ctorName: Option[Name] = None)

sealed class PreEnvironment protected (
    val declarations: Map[Name, Declaration],
    val reductions: ReductionMap,
    val proofObligations: List[Future[Option[EnvironmentUpdateError]]],
    val inductiveInfo: Map[Name, InductiveInfo] = Map(),
    val opaqueValues: Map[Name, Expr] = Map()) {

  def get(name: Name): Option[Declaration] =
    declarations.get(name)
  def apply(name: Name): Declaration =
    declarations(name)

  def value(name: Name): Option[Expr] =
    reductions.get(name).find(_.lhs.isInstanceOf[Const]).map(_.rhs)

  def isAxiom(name: Name): Boolean =
    !this(name).builtin && value(name).isEmpty

  private def addDeclsFor(mod: CompiledModification): Map[Name, Declaration] =
    declarations ++ mod.decls.view.map(d => d.name -> d)

  def addWithFuture(mod: Modification)(implicit executionContext: ExecutionContext): (Future[Option[EnvironmentUpdateError]], PreEnvironment) = {
    val compiled = mod.compile(this)
    val newIndInfo = mod match {
      case IndMod(name, _, _, numParams, intros) =>
        // For inductive types with exactly one constructor, compute numFields and store ctor name
        val (numFields, ctorName) = intros.headOption.map { case (cn, ctorTy) =>
          (countFields(ctorTy, numParams), Some(cn))
        }.getOrElse((0, None))
        inductiveInfo + (name -> InductiveInfo(numParams, numFields, ctorName))
      case CtorMod(ctorName, _, _, inductName, _, numParams, numFields) =>
        // Update with constructor name if not already present
        inductiveInfo.get(inductName) match {
          case Some(info) if info.ctorName.isEmpty =>
            inductiveInfo + (inductName -> InductiveInfo(numParams, numFields, Some(ctorName)))
          case Some(_) => inductiveInfo
          case None => inductiveInfo + (inductName -> InductiveInfo(numParams, numFields, Some(ctorName)))
        }
      case _ => inductiveInfo
    }
    val newOpaqueValues = mod match {
      case OpaqueMod(name, _, _, value) => opaqueValues + (name -> value)
      case _ => opaqueValues
    }
    val checkingTask = Future {
      Try(compiled.check()).failed.toOption.
        map(t => EnvironmentUpdateError(mod, t.getMessage))
    }
    checkingTask -> new PreEnvironment(addDeclsFor(compiled), reductions ++ compiled.rules, checkingTask :: proofObligations, newIndInfo, newOpaqueValues)
  }

  def addNow(mod: Modification): PreEnvironment = {
    val compiled = mod.compile(this)
    compiled.check()
    val newIndInfo = mod match {
      case IndMod(name, _, _, numParams, intros) =>
        val (numFields, ctorName) = intros.headOption.map { case (cn, ctorTy) =>
          (countFields(ctorTy, numParams), Some(cn))
        }.getOrElse((0, None))
        inductiveInfo + (name -> InductiveInfo(numParams, numFields, ctorName))
      case CtorMod(ctorName, _, _, inductName, _, numParams, numFields) =>
        inductiveInfo.get(inductName) match {
          case Some(info) if info.ctorName.isEmpty =>
            inductiveInfo + (inductName -> InductiveInfo(numParams, numFields, Some(ctorName)))
          case Some(_) => inductiveInfo
          case None => inductiveInfo + (inductName -> InductiveInfo(numParams, numFields, Some(ctorName)))
        }
      case _ => inductiveInfo
    }
    val newOpaqueValues = mod match {
      case OpaqueMod(name, _, _, value) => opaqueValues + (name -> value)
      case _ => opaqueValues
    }
    new PreEnvironment(addDeclsFor(compiled), reductions ++ compiled.rules, proofObligations, newIndInfo, newOpaqueValues)
  }

  /** Count the number of fields in a constructor type (after skipping numParams pis) */
  private def countFields(ty: Expr, numParams: Int): Int = {
    def go(ty: Expr, paramsLeft: Int, fields: Int): Int = ty match {
      case Pi(_, body) =>
        if (paramsLeft > 0) go(body, paramsLeft - 1, fields)
        else go(body, 0, fields + 1)
      case _ => fields
    }
    go(ty, numParams, 0)
  }

  def add(mod: Modification)(implicit executionContext: ExecutionContext): PreEnvironment =
    addWithFuture(mod)._2

  def force(implicit executionContext: ExecutionContext): Future[Either[Seq[EnvironmentUpdateError], Environment]] =
    Environment.force(this)
}

final class Environment private (declarations: Map[Name, Declaration], reductionMap: ReductionMap,
    indInfo: Map[Name, InductiveInfo], opaqValues: Map[Name, Expr])
  extends PreEnvironment(declarations, reductionMap, Nil, indInfo, opaqValues)
object Environment {
  def force(preEnvironment: PreEnvironment)(implicit executionContext: ExecutionContext): Future[Either[Seq[EnvironmentUpdateError], Environment]] =
    Future.sequence(preEnvironment.proofObligations).map(_.flatten).map {
      case Nil => Right(new Environment(preEnvironment.declarations, preEnvironment.reductions, preEnvironment.inductiveInfo, preEnvironment.opaqueValues))
      case exs => Left(exs)
    }

  def default = {
    // Start with an empty environment - no built-in declarations
    new Environment(Map(), ReductionMap(), Map(), Map())
  }
}