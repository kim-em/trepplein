package trepplein

import org.specs2.mutable.*

/**
 * Tests for Lean 4 type checking.
 */
class Lean4Test extends Specification {
  // Basic types
  val natType = Const("Nat", Vector())
  val stringType = Const("String", Vector())
  val boolType = Const("Bool", Vector())

  // Nat constructors (Lean 4 style)
  val natZero = Const(Name("Nat", "zero"), Vector())
  val natSucc = Const(Name("Nat", "succ"), Vector())

  // Build a minimal Lean 4 style environment
  def mkLean4Env(): PreEnvironment = {
    var env: PreEnvironment = Environment.default

    // Declare Nat inductive type
    env = env.addNow(IndMod(Name("Nat"), Vector(), Sort(1), 0, Vector(
      Name("Nat", "zero") -> natType,
      Name("Nat", "succ") -> (natType -->: natType)
    )))

    // Explicitly declare Nat constructors (Lean 4 style)
    env = env.addNow(CtorMod(Name("Nat", "zero"), Vector(), natType, Name("Nat"), 0, 0, 0))
    env = env.addNow(CtorMod(Name("Nat", "succ"), Vector(), natType -->: natType, Name("Nat"), 1, 0, 1))

    // Declare String type as an axiom (simplified - full declaration would be opaque)
    env = env.addNow(AxiomMod(Name("String"), Vector(), Sort(1)))

    // Declare Bool with constructors
    env = env.addNow(IndMod(Name("Bool"), Vector(), Sort.Prop, 0, Vector(
      Name("Bool", "false") -> boolType,
      Name("Bool", "true") -> boolType
    )))
    env = env.addNow(CtorMod(Name("Bool", "false"), Vector(), boolType, Name("Bool"), 0, 0, 0))
    env = env.addNow(CtorMod(Name("Bool", "true"), Vector(), boolType, Name("Bool"), 1, 0, 0))

    env
  }

  def numeral(n: Int): Expr =
    if (n == 0) natZero
    else App(natSucc, numeral(n - 1))

  "NatLit inference" in {
    val env = mkLean4Env()
    val tc = new TypeChecker(env)

    tc.infer(NatLit(0)) must beEqualTo(natType)
    tc.infer(NatLit(42)) must beEqualTo(natType)
    tc.infer(NatLit(BigInt("12345678901234567890"))) must beEqualTo(natType)
  }

  "StringLit inference" in {
    val env = mkLean4Env()
    val tc = new TypeChecker(env)

    tc.infer(StringLit("")) must beEqualTo(stringType)
    tc.infer(StringLit("hello world")) must beEqualTo(stringType)
    tc.infer(StringLit("unicode: \u03B1\u03B2\u03B3")) must beEqualTo(stringType)
  }

  "Sort levels" in {
    val env = Environment.default
    val tc = new TypeChecker(env)

    tc.infer(Sort.Prop) must beEqualTo(Sort(1))
    tc.infer(Sort(1)) must beEqualTo(Sort(2))
    tc.infer(Sort(Level.Param("u"))) must beEqualTo(Sort(Level.Succ(Level.Param("u"))))
  }

  "Let expression zeta reduction" in {
    val env = mkLean4Env()
    val tc = new TypeChecker(env)

    // let x : Nat := 5 in x  (using de Bruijn index Var(0) for bound variable)
    val letExpr = Let(Binding("x", natType, BinderInfo.Default), NatLit(5), Var(0))
    tc.checkDefEq(tc.infer(letExpr), natType) must beLike { case IsDefEq => ok }

    // After zeta reduction, let x = 5 in x should equal 5
    tc.checkDefEq(letExpr, NatLit(5)) must beLike { case IsDefEq => ok }
  }

  "Lambda abstraction and application" in {
    val env = mkLean4Env()
    val tc = new TypeChecker(env)

    // fun x : Nat => x  (using de Bruijn index Var(0) for bound variable)
    val id = Lam(Binding("x", natType, BinderInfo.Default), Var(0))
    // The inferred type is Pi (x : Nat), Nat which is definitionally equal to Nat -> Nat
    tc.checkDefEq(tc.infer(id), natType -->: natType) must beLike { case IsDefEq => ok }

    // (fun x => x) 42 should reduce to 42
    tc.checkDefEq(App(id, NatLit(42)), NatLit(42)) must beLike { case IsDefEq => ok }
  }

  "Constructor type inference" in {
    val env = mkLean4Env()
    val tc = new TypeChecker(env)

    tc.infer(natZero) must beEqualTo(natType)
    tc.infer(natSucc) must beEqualTo(natType -->: natType)
    tc.infer(App(natSucc, natZero)) must beEqualTo(natType)
  }

  "Numeral expansion" in {
    val env = mkLean4Env()
    val tc = new TypeChecker(env)

    // 0 should type check as Nat
    tc.infer(numeral(0)) must beEqualTo(natType)
    // 5 = succ(succ(succ(succ(succ(zero))))) should also be Nat
    tc.infer(numeral(5)) must beEqualTo(natType)
  }
}

class ExprTest extends Specification {
  "Expression equality" in {
    NatLit(42) must beEqualTo(NatLit(42))
    NatLit(42) must not(beEqualTo(NatLit(43)))

    StringLit("hello") must beEqualTo(StringLit("hello"))
    StringLit("hello") must not(beEqualTo(StringLit("world")))

    Proj(Name("Prod"), 0, Var(0)) must beEqualTo(Proj(Name("Prod"), 0, Var(0)))
    Proj(Name("Prod"), 0, Var(0)) must not(beEqualTo(Proj(Name("Prod"), 1, Var(0))))
  }

  "Expression instantiation" in {
    val body = Proj(Name("Prod"), 0, Var(0))
    val arg = NatLit(5)
    body.instantiate(arg) must beEqualTo(Proj(Name("Prod"), 0, NatLit(5)))
  }

  "Expression abstraction" in {
    val x = LocalConst(Binding("x", Sort(1), BinderInfo.Default))
    val expr = Proj(Name("Prod"), 0, x)
    expr.abstr(x) must beEqualTo(Proj(Name("Prod"), 0, Var(0)))
  }

  "Expression has locals" in {
    NatLit(42).hasLocals must beEqualTo(false)
    StringLit("hello").hasLocals must beEqualTo(false)

    val x = LocalConst(Binding("x", Sort(1), BinderInfo.Default))
    Proj(Name("Prod"), 0, x).hasLocals must beEqualTo(true)
    Proj(Name("Prod"), 0, NatLit(1)).hasLocals must beEqualTo(false)
  }
}

class LiteralReductionTest extends Specification {
  "Nat.add reduction" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "add"), Vector()),
      List(NatLit(3), NatLit(5))
    )
    result must beSome(NatLit(8))
  }

  "Nat.sub reduction (no underflow)" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "sub"), Vector()),
      List(NatLit(10), NatLit(3))
    )
    result must beSome(NatLit(7))
  }

  "Nat.sub reduction (underflow clamps to 0)" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "sub"), Vector()),
      List(NatLit(3), NatLit(10))
    )
    result must beSome(NatLit(0))
  }

  "Nat.mul reduction" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "mul"), Vector()),
      List(NatLit(7), NatLit(6))
    )
    result must beSome(NatLit(42))
  }

  "Nat.div reduction" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "div"), Vector()),
      List(NatLit(17), NatLit(5))
    )
    result must beSome(NatLit(3))
  }

  "Nat.div by zero returns 0" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "div"), Vector()),
      List(NatLit(10), NatLit(0))
    )
    result must beSome(NatLit(0))
  }

  "String.append reduction" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("String", "append"), Vector()),
      List(StringLit("hello"), StringLit(" world"))
    )
    result must beSome(StringLit("hello world"))
  }

  "String.length reduction" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("String", "length"), Vector()),
      List(StringLit("hello"))
    )
    result must beSome(NatLit(5))
  }

  "No reduction for non-literals" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Nat", "add"), Vector()),
      List(NatLit(3), Var(0))
    )
    result must beNone
  }

  "No reduction for unknown functions" in {
    val result = LiteralReduction.reduceLiteralApp(
      Const(Name("Foo", "bar"), Vector()),
      List(NatLit(3), NatLit(5))
    )
    result must beNone
  }
}

class ParserTest extends Specification {
  "Parse Lean 4 name commands" in {
    // Names: 0 = anonymous (pre-initialized), 1 = "foo", 2 = "bar", 3 = "bar.42"
    val input = """1 #NS 0 foo
2 #NS 0 bar
3 #NI 2 42
"""
    val stream = new java.io.ByteArrayInputStream(input.getBytes("UTF-8"))
    val cmds = TextExportParser.parseStream(stream).toList
    cmds must beEmpty  // Names don't produce commands, just update internal state
  }

  "Parse Lean 4 axiom declaration" in {
    // Levels: 0 = zero (pre-initialized), 1 = succ(0) = 1
    // Names: 0 = anonymous (pre-initialized), 1 = "Nat"
    // Exprs: 0 = Sort(level 1) = Sort(1)
    val input = """1 #NS 0 Nat
1 #US 0
0 #ES 1
#AX 1 0
"""
    val stream = new java.io.ByteArrayInputStream(input.getBytes("UTF-8"))
    val cmds = TextExportParser.parseStream(stream).toList
    cmds.size must beEqualTo(1)
    cmds.head must beLike {
      case ExportedModification(AxiomMod(name, ups, ty)) =>
        name must beEqualTo(Name("Nat"))
        ups must beEmpty
        ty must beEqualTo(Sort(1))
    }
  }
}
