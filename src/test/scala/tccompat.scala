package trepplein

import org.specs2.mutable.*

/**
 * Tests translated from leanprover/tc (Haskell reference type-checker for Lean 3).
 * https://github.com/leanprover/tc
 *
 * Adapted for Lean 4 / trepplein:
 * - GlobalLevel replaced with Level.Param (Lean 4 has no global universe levels)
 * - API translated from Haskell to Scala idioms
 */

// =============================================================================
// LevelSpec.hs translations
// =============================================================================

class LevelTest extends Specification {
  import Level._

  val lp1 = Param(Name("l1"))
  val lp2 = Param(Name("l2"))
  // In tc these were GlobalLevel, adapted to Param for Lean 4
  val gp1 = Param(Name("g1"))
  val gp2 = Param(Name("g2"))

  def mkIteratedSucc(l: Level, k: Int): Level =
    if (k <= 0) l else Succ(mkIteratedSucc(l, k - 1))

  // levelHasParamSpec - 6 tests
  "levelHasParam (Level.univParams)" should {
    "return empty for iterated Succ of a single param treated as 'global'" in {
      // Original: gp1 was GlobalLevel, levelHasParam returned false
      // For Lean 4: Param always counts, so this tests the traversal works
      val l0 = mkIteratedSucc(gp1, 3)
      l0.univParams.contains(gp1) must beTrue
    }

    "recurse under Succ" in {
      val l1 = mkIteratedSucc(lp1, 4)
      l1.univParams.contains(lp1) must beTrue
    }

    "recurse under succ and max when param present" in {
      val l2 = mkIteratedSucc(Max(lp1, gp1), 2)
      l2.univParams.contains(lp1) must beTrue
      l2.univParams.contains(gp1) must beTrue
    }

    "return both params under nested max" in {
      val l3 = mkIteratedSucc(Max(gp1, gp2), 2)
      l3.univParams.contains(gp1) must beTrue
      l3.univParams.contains(gp2) must beTrue
    }

    "handle nested max" in {
      val l4 = Max(gp1, Max(gp2, Zero))
      l4.univParams.contains(gp1) must beTrue
      l4.univParams.contains(gp2) must beTrue
    }

    "recurse under nested imax" in {
      val l5 = IMax(gp1, IMax(lp1, lp2))
      l5.univParams.contains(gp1) must beTrue
      l5.univParams.contains(lp1) must beTrue
      l5.univParams.contains(lp2) must beTrue
    }
  }

  // instantiateLevelSpec - 2 tests
  "Level.instantiate" should {
    "substitute level params" in {
      val lp3 = Param(Name("lp3"))
      val oldLevel = Max(lp1, Max(lp2, lp3))

      // Substitute lp1 -> Zero, lp2 -> lp3
      // Result should simplify: Max(Zero, Max(lp3, lp3)) = lp3
      val newLevel1 = oldLevel.instantiate(Map(lp1 -> Zero, lp2 -> lp3))
      (newLevel1 === lp3) must beTrue
    }

    "work when substituting with existing level params" in {
      val lp3 = Param(Name("lp3"))
      val oldLevel = Max(lp1, Max(lp2, lp3))

      // Swap lp1 and lp2
      val newLevel2 = oldLevel.instantiate(Map(lp1 -> lp2, lp2 -> lp1))
      // Result: Max(lp2, Max(lp1, lp3)) should be equivalent to original
      (newLevel2 === Max(lp2, Max(lp1, lp3))) must beTrue
    }
  }

  // levelsMiscSpec - 4 tests
  // Note: trepplein's Level case classes don't auto-simplify on construction
  // Use .simplify or === for equivalence checks
  "Level misc operations" should {
    val zero = Zero
    val one = Succ(zero)
    val two = Succ(one)
    val p1 = Param(Name("p1"))
    val p2 = Param(Name("p2"))

    "simplify Max of explicit levels" in {
      // Max(1, 2).simplify = 2
      Max(one, two).simplify must beEqualTo(two)
      (Max(one, two) === two) must beTrue
    }

    "simplify IMax correctly" in {
      // IMax(1, 2).simplify = 2  (second arg is Succ, so becomes Max)
      IMax(one, two).simplify must beEqualTo(two)
      // IMax(_, 0).simplify = 0
      IMax(two, zero).simplify must beEqualTo(zero)
      IMax(p1, zero).simplify must beEqualTo(zero)
    }

    "simplify Max with zero" in {
      // Max(0, p1).simplify = p1
      Max(zero, p1).simplify must beEqualTo(p1)
      Max(p1, zero).simplify must beEqualTo(p1)
    }

    "check level equivalence" in {
      (one === Succ(zero)) must beTrue
      (zero === two) must beFalse
      (zero === p2) must beFalse
    }

    "normalize max(p, succ(p)) to succ(p)" in {
      (Succ(p2) === Max(p2, Succ(p2))) must beTrue
    }

    "normalize max to be commutative" in {
      (Max(p1, p2) === Max(p2, p1)) must beTrue
    }

    "not normalize imax (it's not commutative)" in {
      (IMax(p1, p2) === IMax(p2, p1)) must beFalse
    }

    "mkIMax should delegate to mkMax when second arg is definitely not zero" in {
      (IMax(Succ(p1), Succ(p2)) === IMax(Succ(p2), Succ(p1))) must beTrue
    }
  }

  // normalizeSpec1 - 5 tests
  "Level normalization" should {
    val u = Param(Name("u"))
    val v = Param(Name("v"))
    val z = Zero
    val one = Succ(z)
    val two = Succ(one)

    "ignore zeros in max" in {
      // max(0, max(u, 1)) should be equivalent to max(1, u)
      val l = Max(z, Max(u, one))
      (l === Max(one, u)) must beTrue
    }

    "normalize nested max with succ" in {
      // max(max(succ(v), u), max(v, succ(u))) = max(succ(u), succ(v))
      val l = Max(Max(Succ(v), u), Max(v, Succ(u)))
      (l === Max(Succ(u), Succ(v))) must beTrue
    }

    "preserve max(succ(0), u)" in {
      val l = Max(Succ(Zero), u)
      (l === Max(Succ(Zero), u)) must beTrue
    }

    "normalize deeply nested max with succ" in {
      // max(succ(max(succ(v), u)), max(v, succ(succ(u)))) = max(succ(succ(u)), succ(succ(v)))
      val l = Max(Succ(Max(Succ(v), u)), Max(v, Succ(Succ(u))))
      (l === Max(Succ(Succ(u)), Succ(Succ(v)))) must beTrue
    }

    "remove irrelevant explicit levels" in {
      // max(succ(u), max(max(u, 1), max(1, u))) = succ(u)
      val l = Max(Succ(u), Max(Max(u, one), Max(one, u)))
      (l === Succ(u)) must beTrue
    }
  }

  // levelNotBiggerThanSpec1 - 1 test
  "Level comparison (<=)" should {
    val u = Param(Name("u"))

    "work with max on the rhs" in {
      (u <== Max(Succ(Zero), u)) must beTrue
    }

    "handle zero <= anything" in {
      (Zero <== u) must beTrue
      (Zero <== Succ(u)) must beTrue
    }

    "handle succ comparison" in {
      (u <== Succ(u)) must beTrue
      (Succ(u) <== u) must beFalse
    }
  }
}

// =============================================================================
// ExprSpec.hs translations
// =============================================================================

class ExprVarBoundTest extends Specification {
  val c1 = Const(Name("c1"), Vector())
  val c2 = Const(Name("c2"), Vector())
  val mkType = Sort(Level.Succ(Level.Zero))

  // getFreeVarRangeSpec - 5 tests
  "Expr.varBound (getFreeVarRange)" should {
    "be 0 for constants" in {
      c1.varBound must beEqualTo(0)
    }

    "be 1+varIdx for Vars inside Apps" in {
      val e2 = App(c1, Var(1))
      e2.varBound must beEqualTo(2)
    }

    "be 0 for sorts" in {
      val e3 = Sort(Level.Zero)
      e3.varBound must beEqualTo(0)
    }

    "decrement for each lambda" in {
      // Lam binds one var, so Var(1) inside becomes effectively Var(0) relative
      // varBound of Lam(_, Var(1)) = max(0, 1-1+1) = 1
      val e4 = Lam(Binding(Name("x"), Sort(Level.Zero), BinderInfo.Default), App(c1, Var(1)))
      e4.varBound must beEqualTo(1)
    }

    "decrement for each pi" in {
      val e4 = Lam(Binding(Name("x"), Sort(Level.Zero), BinderInfo.Default), App(c1, Var(1)))
      val e5 = Pi(Binding(Name("y"), Sort(Level.Zero), BinderInfo.Default), e4)
      e5.varBound must beEqualTo(0)
    }
  }

  // exprHasLevelParamSpec - 4 tests
  "Expr.univParams (exprHasLevelParam)" should {
    val lp1 = Level.Param(Name("l1"))
    val gp1 = Level.Param(Name("g1")) // Was GlobalLevel in tc
    val level1 = Level.Succ(Level.Succ(Level.IMax(lp1, Level.Succ(Level.Succ(Level.Zero)))))
    val level2 = Level.Succ(Level.Succ(Level.Succ(Level.Max(Level.Succ(Level.Zero), gp1))))

    val const1 = Const(Name("c1"), Vector(level1))
    val const2 = Const(Name("c2"), Vector(level2))
    val const12 = Const(Name("c12"), Vector(level1, level2))

    "be non-empty for constants with level params" in {
      val e1 = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), const1)
      e1.univParams.nonEmpty must beTrue
      e1.univParams.contains(lp1) must beTrue
    }

    "find params in const2 (originally was GlobalLevel, now Param)" in {
      val e2 = Pi(Binding(Name("x"), const2, BinderInfo.Default), const2)
      e2.univParams.contains(gp1) must beTrue
    }

    "find all params when multiple present" in {
      val e2 = Pi(Binding(Name("x"), const2, BinderInfo.Default), const2)
      val e12 = Pi(Binding(Name("y"), const12, BinderInfo.Default), e2)
      e12.univParams.contains(lp1) must beTrue
      e12.univParams.contains(gp1) must beTrue
    }

    "find params in Sort" in {
      val e3 = Pi(Binding(Name("z"), Sort(lp1), BinderInfo.Default), const2)
      e3.univParams.contains(lp1) must beTrue
    }
  }

  // instantiateSpec - 4 tests
  // Note: trepplein's instantiate has different semantics than tc's:
  // - tc's instantiate replaces Var(0) and decrements all higher vars
  // - trepplein's instantiate(e) replaces Var(0) only, leaving other vars unchanged
  // These tests are adapted to trepplein's semantics
  "Expr.instantiate" should {
    "replace Var(0) with substitution" in {
      // Simple substitution: (fun _ => Var(0)).instantiate(c1) replaces the bound Var(0)
      // But we're substituting into the whole lambda, so Var(0) outside gets c1
      val e = Var(0)
      val ret = e.instantiate(c1)
      ret must beEqualTo(c1)
    }

    "not affect Var(i) where i > 0 when substituting single value" in {
      // Var(1) is NOT replaced when we instantiate with a single value
      val e = App(Var(0), Var(1))
      val ret = e.instantiate(c1)
      // Var(0) -> c1, Var(1) stays as Var(1) in trepplein
      ret must beEqualTo(App(c1, Var(1)))
    }

    "handle substitution under binders correctly" in {
      // When going under a binder, the offset increases
      // (fun _ => Var(1)).instantiate(c1):
      //   - Var(1) inside the lambda is at offset 1, so it becomes Var(0) relative to outer scope
      //   - We're substituting Var(0) at offset 0, which is Var(1) inside the lambda
      val e = Lam(Binding(Name("_"), mkType, BinderInfo.Default), Var(1))
      val ret = e.instantiate(c1)
      // Var(1) inside the lambda corresponds to Var(0) outside, so it gets replaced
      val expected = Lam(Binding(Name("_"), mkType, BinderInfo.Default), c1)
      ret must beEqualTo(expected)
    }

    "preserve Var(0) inside lambda (bound variable)" in {
      // (fun x => x).instantiate(c1) - the Var(0) inside is bound, not affected
      val e = Lam(Binding(Name("x"), mkType, BinderInfo.Default), Var(0))
      val ret = e.instantiate(c1)
      // Var(0) at offset 1 is < 0+1, so it's the bound variable, unchanged
      ret must beEqualTo(e)
    }
  }

  // instantiateLevelParamsSpec - 2 tests
  "Expr level param instantiation" should {
    val lp1 = Level.Param(Name("l1"))
    val gp1 = Level.Param(Name("g1"))
    val level1 = Level.Succ(Level.Succ(Level.IMax(lp1, Level.Succ(Level.Succ(Level.Zero)))))
    val level2 = Level.Succ(Level.Succ(Level.Succ(Level.Max(Level.Succ(Level.Zero), gp1))))

    val const1 = Const(Name("c1"), Vector(level1))
    val e1 = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), const1)

    "substitute level params in expressions" in {
      val result = e1.instantiate(Map(lp1 -> level2))
      val expectedLevel = Level.Succ(Level.Succ(Level.IMax(level2, Level.Succ(Level.Succ(Level.Zero)))))
      val expectedConst = Const(Name("c1"), Vector(expectedLevel))
      val expected = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), expectedConst)
      result must beEqualTo(expected)
    }

    "work when substituting with the same level params" in {
      val result = e1.instantiate(Map(lp1 -> level1))
      val expectedLevel = Level.Succ(Level.Succ(Level.IMax(level1, Level.Succ(Level.Succ(Level.Zero)))))
      val expectedConst = Const(Name("c1"), Vector(expectedLevel))
      val expected = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), expectedConst)
      result must beEqualTo(expected)
    }
  }

  // appSeqSpec - 3 tests
  "Apps pattern (appSeq)" should {
    val cs = (1 to 4).map(i => Const(Name(s"c$i"), Vector())).toList

    "decompose and reconstruct correctly" in {
      val e = App(App(App(cs(0), cs(1)), cs(2)), cs(3))
      val Apps(op, args) = e
      op must beEqualTo(cs(0))
      args must beEqualTo(List(cs(1), cs(2), cs(3)))
      Apps(op, args) must beEqualTo(e)
    }

    "return e itself as operator when not an App" in {
      val s = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), Var(2))
      s match {
        case Apps(op, args) =>
          op must beEqualTo(s)
          args must beEmpty
      }
    }

    "return empty args when not an App" in {
      val s = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), Var(2))
      s match {
        case Apps(_, args) => args must beEmpty
      }
    }
  }

  // innerBodyOfLambdaSpec - 2 tests
  "Lambda body extraction" should {
    val c = Const(Name("c"), Vector())

    def innerBody(e: Expr): Expr = e match {
      case Lam(_, body) => innerBody(body)
      case _ => e
    }

    "return body of nested lambdas" in {
      val e = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default),
        Lam(Binding(Name("y"), mkType, BinderInfo.Default), c))
      innerBody(e) must beEqualTo(c)
    }

    "do nothing on constants" in {
      val e = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default),
        Lam(Binding(Name("y"), mkType, BinderInfo.Default), c))
      val body = innerBody(e)
      innerBody(body) must beEqualTo(body)
    }
  }
}

// =============================================================================
// TypeCheckerSpec.hs translations
// =============================================================================

class TypeCheckerInferenceTest extends Specification {
  val mkType = Sort(Level.Succ(Level.Zero))
  val mkType2 = Sort(Level.Succ(Level.Succ(Level.Zero)))

  def mkEnv: PreEnvironment = Environment.default

  // inferLambda1
  "inferType for lambda" should {
    "infer Prop -> Type for (fun x : Prop => Prop)" in {
      val env = mkEnv
      val tc = new TypeChecker(env)
      val lam1 = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), Sort.Prop)
      val result = tc.infer(lam1)
      // Should be Pi(_ : Prop, Type) which is Prop -> Type
      result match {
        case Pi(Binding(_, dom, _), body) =>
          dom must beEqualTo(Sort.Prop)
          body must beEqualTo(mkType)
        case _ => ko("Expected Pi type")
      }
    }
  }

  // inferApp1
  "inferType for application" should {
    "infer correct type for (fun x : Type => x) Prop" in {
      val env = mkEnv
      val tc = new TypeChecker(env)
      val lam1 = Lam(Binding(Name("x"), mkType, BinderInfo.Default), Var(0))
      val app1 = App(lam1, Sort.Prop)
      val result = tc.infer(app1)
      // (fun x : Type => x) Prop should have type Type
      result must beEqualTo(mkType)
    }
  }

  // inferConst1
  "inferType for constants" should {
    "look up declared axiom type" in {
      var env = mkEnv
      val axType = Pi(Binding(Name("_"), mkType, BinderInfo.Default), Sort.Prop)
      val axName = Name("ax1")
      env = env.addNow(AxiomMod(axName, Vector(), axType))
      val tc = new TypeChecker(env)
      val result = tc.infer(Const(axName, Vector()))
      result must beEqualTo(axType)
    }
  }
}

class TypeCheckerErrorTest extends Specification {
  def mkEnv: PreEnvironment = Environment.default

  // triggerExceptions - 12 tests
  // Note: UndefGlobalLevel test skipped (Lean 4 has no global levels)

  "TypeChecker error detection" should {
    "throw on undefined level param" in {
      val lp = Level.Param(Name("undef"))
      val decl = AxiomMod(Name("bad"), Vector(), Sort(lp))
      decl.compile(mkEnv).check() must throwA[Exception]
    }

    "throw on TypeExpected (lambda used as type annotation)" in {
      // Trying to declare an axiom with a lambda as its type (not a valid type)
      val e = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), Sort.Prop)
      val decl = AxiomMod(Name("bad"), Vector(), e)
      decl.compile(mkEnv).check() must throwA[Exception]
    }

    "throw on FunctionExpected (applying Prop to Prop)" in {
      val tc = new TypeChecker(mkEnv)
      tc.infer(App(Sort.Prop, Sort.Prop)) must throwA[Exception]
    }

    "throw on TypeMismatchAtApp" in {
      val tc = new TypeChecker(mkEnv)
      // (fun x : Prop => x) applied to Prop itself is valid
      // (fun x : Prop => x) applied to Type is a type mismatch
      val lam = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), Var(0))
      tc.infer(App(lam, Sort(Level.Succ(Level.Zero)))) must throwA[Exception]
    }

    "throw on TypeMismatchAtDef" in {
      // Definition with value that doesn't match declared type
      val ty = Pi(Binding(Name("_"), Sort(Level.Succ(Level.Zero)), BinderInfo.Default), Sort(Level.Succ(Level.Zero)))
      val value = Lam(Binding(Name("x"), Sort.Prop, BinderInfo.Default), Sort.Prop)
      val decl = DefMod(Name("bad"), Vector(), ty, value, ReducibilityHints.Regular(0))
      decl.compile(mkEnv).check() must throwA[Exception]
    }

    "throw on DeclHasFreeVars" in {
      val decl = AxiomMod(Name("bad"), Vector(), Var(0))
      decl.compile(mkEnv).check() must throwA[Exception]
    }

    "throw on DeclHasLocals" in {
      val local = LocalConst(Binding(Name("x"), Sort.Prop, BinderInfo.Default))
      val decl = AxiomMod(Name("bad"), Vector(), local)
      decl.compile(mkEnv).check() must throwA[Exception]
    }

    "throw on NameAlreadyDeclared" in {
      var env = mkEnv
      env = env.addNow(AxiomMod(Name("dup"), Vector(), Sort.Prop))
      val decl = AxiomMod(Name("dup"), Vector(), Sort.Prop)
      decl.compile(env).check() must throwA[Exception]
    }

    "throw on duplicate level param names" in {
      val n = Name("u")
      val lp = Level.Param(n)
      val decl = AxiomMod(Name("bad"), Vector(lp, lp), Sort(lp))
      decl.compile(mkEnv).check() must throwA[Exception]
    }

    "throw on ConstNotFound" in {
      val tc = new TypeChecker(mkEnv)
      tc.infer(Const(Name("not-found"), Vector())) must throwA[Exception]
    }

    "throw on ConstHasWrongNumLevels" in {
      var env = mkEnv
      // Declare axiom with 0 level params
      env = env.addNow(AxiomMod(Name("ax"), Vector(), Sort.Prop))
      val tc = new TypeChecker(env)
      // Try to use it with 1 level arg
      tc.infer(Const(Name("ax"), Vector(Level.Zero))) must throwA[Exception]
    }
  }
}
