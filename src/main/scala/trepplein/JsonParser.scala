package trepplein

import spray.json._
import java.io.{BufferedReader, FileReader, InputStream, InputStreamReader}
import scala.collection.mutable

/**
 * Parser for Lean 4 NDJSON export format.
 *
 * Format reference: https://github.com/leanprover/lean4export/pull/10
 *
 * The NDJSON format consists of one JSON object per line:
 * - First line: metadata with exporter and Lean version info
 * - Subsequent lines: names, levels, expressions, and declarations
 *
 * Each object has an "i" field for its index (used for referencing)
 * and a type-specific field indicating what kind of object it is.
 */
object JsonExportParser {
  import DefaultJsonProtocol._

  def parseFile(filename: String): LazyList[ExportFileCommand] = {
    val reader = new BufferedReader(new FileReader(filename))
    parseReader(reader)
  }

  def parseStream(in: InputStream): LazyList[ExportFileCommand] = {
    val reader = new BufferedReader(new InputStreamReader(in, "UTF-8"))
    parseReader(reader)
  }

  def parseReader(reader: BufferedReader): LazyList[ExportFileCommand] = {
    val state = new ParserState()

    def readLines(): LazyList[String] = {
      val line = reader.readLine()
      if (line == null) LazyList.empty
      else line #:: readLines()
    }

    readLines()
      .flatMap(line => parseLine(state, line))
  }

  private class ParserState {
    val names: mutable.ArrayBuffer[Name] = mutable.ArrayBuffer[Name]()
    val levels: mutable.ArrayBuffer[Level] = mutable.ArrayBuffer[Level]()
    val exprs: mutable.ArrayBuffer[Expr] = mutable.ArrayBuffer[Expr]()
    val recRules: mutable.ArrayBuffer[RecRule] = mutable.ArrayBuffer[RecRule]()

    // Pre-initialize index 0 with anonymous name and level zero
    names += Name.Anon
    levels += Level.Zero

    def getName(idx: Int): Name = names(idx)
    def getLevel(idx: Int): Level = levels(idx)
    def getExpr(idx: Int): Expr = exprs(idx)
    def getRecRule(idx: Int): RecRule = recRules(idx)

    def setName(idx: Int, n: Name): Unit = { ensureSize(names, idx, Name.Anon); names(idx) = n }
    def setLevel(idx: Int, l: Level): Unit = { ensureSize(levels, idx, Level.Zero); levels(idx) = l }
    def setExpr(idx: Int, e: Expr): Unit = { ensureSize(exprs, idx, Sort.Prop); exprs(idx) = e }
    def setRecRule(idx: Int, r: RecRule): Unit = { ensureSize(recRules, idx, r); recRules(idx) = r }

    private def ensureSize[T](buf: mutable.ArrayBuffer[T], idx: Int, default: T): Unit = {
      while (buf.size <= idx) buf += default
    }
  }

  private def parseLine(state: ParserState, line: String): Option[ExportFileCommand] = {
    if (line.isEmpty) return None

    val json = line.parseJson.asJsObject
    val fields = json.fields

    // Check for metadata line
    if (fields.contains("meta")) {
      // Skip metadata for now
      return None
    }

    // Get the index if present
    val idx = fields.get("i").map(_.convertTo[Int]).getOrElse(-1)

    // Parse based on the type field present
    if (fields.contains("str")) {
      // Name.str: {"str": {"pre": int, "str": string}, "i": int}
      val strObj = fields("str").asJsObject
      val pre = strObj.fields("pre").convertTo[Int]
      val s = strObj.fields("str").convertTo[String]
      state.setName(idx, Name.Str(state.getName(pre), s))
      None
    } else if (fields.contains("num")) {
      // Name.num: {"num": {"pre": int, "i": int}, "i": int}
      val numObj = fields("num").asJsObject
      val pre = numObj.fields("pre").convertTo[Int]
      val i = numObj.fields("i").convertTo[Long]
      state.setName(idx, Name.Num(state.getName(pre), i))
      None
    } else if (fields.contains("succ")) {
      // Level.succ: {"succ": int, "i": int}
      val pred = fields("succ").convertTo[Int]
      state.setLevel(idx, Level.Succ(state.getLevel(pred)))
      None
    } else if (fields.contains("max")) {
      // Level.max: {"max": [int, int], "i": int}
      val arr = fields("max").convertTo[JsArray].elements
      val l1 = arr(0).convertTo[Int]
      val l2 = arr(1).convertTo[Int]
      state.setLevel(idx, Level.Max(state.getLevel(l1), state.getLevel(l2)))
      None
    } else if (fields.contains("imax")) {
      // Level.imax: {"imax": [int, int], "i": int}
      val arr = fields("imax").convertTo[JsArray].elements
      val l1 = arr(0).convertTo[Int]
      val l2 = arr(1).convertTo[Int]
      state.setLevel(idx, Level.IMax(state.getLevel(l1), state.getLevel(l2)))
      None
    } else if (fields.contains("param")) {
      // Level.param: {"param": int, "i": int}
      val nameIdx = fields("param").convertTo[Int]
      state.setLevel(idx, Level.Param(state.getName(nameIdx)))
      None
    } else if (fields.contains("bvar")) {
      // Expr.bvar: {"bvar": {"deBruijnIndex": int}, "i": int}
      val bvarObj = fields("bvar").asJsObject
      val dbi = bvarObj.fields("deBruijnIndex").convertTo[Int]
      state.setExpr(idx, Var(dbi))
      None
    } else if (fields.contains("sort")) {
      // Expr.sort: {"sort": {"u": int}, "i": int}
      val sortObj = fields("sort").asJsObject
      val u = sortObj.fields("u").convertTo[Int]
      state.setExpr(idx, Sort(state.getLevel(u)))
      None
    } else if (fields.contains("const")) {
      // Expr.const: {"const": {"declName": int, "us": [int]}, "i": int}
      val constObj = fields("const").asJsObject
      val nameIdx = constObj.fields("declName").convertTo[Int]
      val usIdxs = constObj.fields("us").convertTo[Vector[Int]]
      state.setExpr(idx, Const(state.getName(nameIdx), usIdxs.map(state.getLevel)))
      None
    } else if (fields.contains("app")) {
      // Expr.app: {"app": {"fn": int, "arg": int}, "i": int}
      val appObj = fields("app").asJsObject
      val fn = appObj.fields("fn").convertTo[Int]
      val arg = appObj.fields("arg").convertTo[Int]
      state.setExpr(idx, App(state.getExpr(fn), state.getExpr(arg)))
      None
    } else if (fields.contains("lam")) {
      // Expr.lam: {"lam": {...}, "i": int}
      val lamObj = fields("lam").asJsObject
      val binderName = lamObj.fields("binderName").convertTo[Int]
      val binderType = lamObj.fields("binderType").convertTo[Int]
      val body = lamObj.fields("body").convertTo[Int]
      val binderInfo = parseBinderInfo(lamObj.fields("binderInfo").convertTo[String])
      state.setExpr(idx, Lam(Binding(state.getName(binderName), state.getExpr(binderType), binderInfo), state.getExpr(body)))
      None
    } else if (fields.contains("forallE")) {
      // Expr.forallE/Pi: {"forallE": {...}, "i": int}
      val piObj = fields("forallE").asJsObject
      val binderName = piObj.fields("binderName").convertTo[Int]
      val binderType = piObj.fields("binderType").convertTo[Int]
      val body = piObj.fields("body").convertTo[Int]
      val binderInfo = parseBinderInfo(piObj.fields("binderInfo").convertTo[String])
      state.setExpr(idx, Pi(Binding(state.getName(binderName), state.getExpr(binderType), binderInfo), state.getExpr(body)))
      None
    } else if (fields.contains("letE")) {
      // Expr.letE: {"letE": {...}, "i": int}
      val letObj = fields("letE").asJsObject
      val declName = letObj.fields("declName").convertTo[Int]
      val ty = letObj.fields("type").convertTo[Int]
      val value = letObj.fields("value").convertTo[Int]
      val body = letObj.fields("body").convertTo[Int]
      state.setExpr(idx, Let(Binding(state.getName(declName), state.getExpr(ty), BinderInfo.Default), state.getExpr(value), state.getExpr(body)))
      None
    } else if (fields.contains("proj")) {
      // Expr.proj: {"proj": {"typeName": int, "idx": int, "struct": int}, "i": int}
      val projObj = fields("proj").asJsObject
      val typeName = projObj.fields("typeName").convertTo[Int]
      val projIdx = projObj.fields("idx").convertTo[Int]
      val struct = projObj.fields("struct").convertTo[Int]
      state.setExpr(idx, Proj(state.getName(typeName), projIdx, state.getExpr(struct)))
      None
    } else if (fields.contains("natVal")) {
      // Expr.natVal: {"natVal": string, "i": int}
      val nStr = fields("natVal").convertTo[String]
      state.setExpr(idx, NatLit(BigInt(nStr)))
      None
    } else if (fields.contains("strVal")) {
      // Expr.strVal: {"strVal": string, "i": int}
      val s = fields("strVal").convertTo[String]
      state.setExpr(idx, StringLit(s))
      None
    } else if (fields.contains("axiomInfo")) {
      // Declaration: axiom
      val info = fields("axiomInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      Some(ExportedModification(AxiomMod(name, ups, ty)))
    } else if (fields.contains("defnInfo")) {
      // Declaration: definition
      val info = fields("defnInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val value = state.getExpr(info("value").convertTo[Int])
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      val hints = info.get("hints") match {
        case Some(JsString("opaque")) => ReducibilityHints.Opaque
        case Some(JsString("abbrev")) => ReducibilityHints.Abbrev
        case Some(JsNumber(n)) => ReducibilityHints.Regular(n.toInt)
        case _ => ReducibilityHints.Regular(0)
      }
      Some(ExportedModification(DefMod(name, ups, ty, value, hints)))
    } else if (fields.contains("thmInfo")) {
      // Declaration: theorem
      val info = fields("thmInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val value = state.getExpr(info("value").convertTo[Int])
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      Some(ExportedModification(TheoremMod(name, ups, ty, value)))
    } else if (fields.contains("opaqueInfo")) {
      // Declaration: opaque
      val info = fields("opaqueInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val value = state.getExpr(info("value").convertTo[Int])
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      Some(ExportedModification(OpaqueMod(name, ups, ty, value)))
    } else if (fields.contains("quotInfo")) {
      // Declaration: quotient
      Some(ExportedModification(QuotMod))
    } else if (fields.contains("inductInfo")) {
      // Declaration: inductive
      val info = fields("inductInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val numParams = info("numParams").convertTo[Int]
      val ctors = info("ctors").convertTo[Vector[Int]].map(state.getName)
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      // Simplified: constructor types will come from separate ctorInfo
      Some(ExportedModification(IndMod(name, ups, ty, numParams, ctors.map(cn => (cn, Sort.Prop)))))
    } else if (fields.contains("ctorInfo")) {
      // Declaration: constructor
      val info = fields("ctorInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val inductName = state.getName(info("induct").convertTo[Int])
      val cidx = info("cidx").convertTo[Int]
      val numParams = info("numParams").convertTo[Int]
      val numFields = info("numFields").convertTo[Int]
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      Some(ExportedModification(CtorMod(name, ups, ty, inductName, cidx, numParams, numFields)))
    } else if (fields.contains("recInfo")) {
      // Declaration: recursor
      val info = fields("recInfo").asJsObject.fields
      val name = state.getName(info("name").convertTo[Int])
      val ty = state.getExpr(info("type").convertTo[Int])
      val inductNames = info("all").convertTo[Vector[Int]].map(state.getName)
      val numParams = info("numParams").convertTo[Int]
      val numIndices = info("numIndices").convertTo[Int]
      val numMotives = info("numMotives").convertTo[Int]
      val numMinors = info("numMinors").convertTo[Int]
      val isK = info("k").convertTo[Boolean]
      val ups = info("levelParams").convertTo[Vector[Int]].map(i => Level.Param(state.getName(i)))
      val rules = info("rules").convertTo[Vector[Int]].map(state.getRecRule)
      Some(ExportedModification(RecursorMod(name, ups, ty, inductNames, numParams, numIndices, numMotives, numMinors, recRules = rules, isK)))
    } else if (fields.contains("recRule")) {
      // Recursor rule
      val ruleObj = fields("recRule").asJsObject.fields
      val ctor = state.getName(ruleObj("ctor").convertTo[Int])
      val nfields = ruleObj("nfields").convertTo[Int]
      val rhs = state.getExpr(ruleObj("rhs").convertTo[Int])
      state.setRecRule(idx, RecRule(ctor, nfields, rhs))
      None
    } else {
      // Unknown type, skip
      None
    }
  }

  private def parseBinderInfo(s: String): BinderInfo = s match {
    case "default" => BinderInfo.Default
    case "implicit" => BinderInfo.Implicit
    case "instImplicit" => BinderInfo.InstImplicit
    case "strictImplicit" => BinderInfo.StrictImplicit
    case _ => BinderInfo.Default
  }
}
