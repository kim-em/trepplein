package trepplein

import java.io.{FileInputStream, InputStream}
import java.nio.charset.Charset

import scala.annotation.tailrec
import scala.collection.mutable

sealed trait ExportFileCommand
case class ExportedModification(modification: Modification) extends ExportFileCommand
case class ExportedNotation(notation: Notation) extends ExportFileCommand
// Lean 4: recursor rules are parsed separately and referenced by index
case class ExportedRecRule(rule: RecRule) extends ExportFileCommand
// Format 3.0: bundled inductive/ctor/recursor declarations
case class ExportedBundle(modifications: Vector[Modification]) extends ExportFileCommand

/**
 * Parser for Lean 4 text export format.
 *
 * Format reference: https://github.com/leanprover/lean4export
 *
 * Key differences from Lean 3:
 * - Names and levels are indexed starting at 0 (anonymous/zero pre-initialized)
 * - Binder info uses #BD, #BI, #BS, #BC prefixes
 * - New expression types: #EJ (Proj), #ELN (NatLit), #ELS (StringLit)
 * - New declarations: #THM, #OPAQ, #CTOR, #REC with explicit recursor rules
 * - Definitions include reducibility hints (O/A/R n)
 */
private class TextExportParser {
  val name: mutable.ArrayBuffer[Name] = mutable.ArrayBuffer[Name]()
  val level: mutable.ArrayBuffer[Level] = mutable.ArrayBuffer[Level]()
  val expr: mutable.ArrayBuffer[Expr] = mutable.ArrayBuffer[Expr]()
  val recRule: mutable.ArrayBuffer[RecRule] = mutable.ArrayBuffer[RecRule]()

  // Lean 4: name[0] = anonymous, level[0] = zero (pre-initialized)
  name += Name.Anon
  level += Level.Zero

  @tailrec final def write[T](b: mutable.ArrayBuffer[T], i: Int, t: T, default: T): Unit =
    b.size match {
      case `i` => b += t
      case s if s < i =>
        b += default
        write(b, i, t, default)
      case s if s > i =>
        b(i) = t
    }
}

private class LinesParser(textExportParser: TextExportParser, bytes: Array[Byte], end: Int) {
  import textExportParser._

  var index = 0
  def hasNext(): Boolean = index < end
  def cur(): Char = bytes(index).toChar
  def next(): Char = {
    if (!hasNext()) throw new IndexOutOfBoundsException
    val c = cur()
    index += 1
    c
  }

  def peek(): Char = if (hasNext()) cur() else '\n'

  def consume(c: Char): Unit = if (next() != c) throw new IllegalArgumentException(s"expected $c, got ${cur()}")
  def consume(s: String): Unit = s.foreach(consume)

  def lines(): Vector[ExportFileCommand] = {
    val out = Vector.newBuilder[ExportFileCommand]
    while (hasNext()) {
      line().foreach(out += _)
      // Skip to end of line (handle blank lines and trailing content)
      while (hasNext() && cur() != '\n') next()
      if (hasNext()) next() // consume the newline
    }
    out.result()
  }

  def line(): Option[ExportFileCommand] = {
    // Skip leading whitespace
    while (hasNext() && (cur() == ' ' || cur() == '\r')) next()
    if (!hasNext() || cur() == '\n') return None

    next() match {
      case c if '0' <= c && c <= '9' =>
        // Could be indexed definition or version line
        val n = long(c - '0').toInt
        if (peek() == '.') {
          // Version line like "2.0.0" - validate major version is 2
          require(n == 2, s"Unsupported export format version $n (expected 2.x.x)")
          rest()
          return None
        }
        consume(' '); consume('#')
        next() match {
          case 'N' =>
            // Name: #NS or #NI (use interning factory methods for reference equality)
            next() match {
              case 'S' => write(name, n, Name.mkStr(spc(nameRef()), spc(rest())), Name.Anon)
              case 'I' => write(name, n, Name.mkNum(spc(nameRef()), spc(long())), Name.Anon)
            }
          case 'U' =>
            // Level: #US, #UM, #UIM, #UP
            write(level, n, levelDef(), Level.Zero)
          case 'E' =>
            // Expression: #EV, #ES, #EC, #EA, #EL, #EP, #EZ, #EJ, #ELN, #ELS
            write(expr, n, exprDef(), Sort.Prop)
          case 'R' =>
            // Recursor rule: #RR
            consume('R')
            val ctorName = spc(nameRef())
            val nfields = spc(num())
            val rhs = spc(exprRef())
            val rule = RecRule(ctorName, nfields, rhs)
            write(recRule, n, rule, rule)
        }
        None
      case '#' =>
        // Declaration command
        Some(declarationDef())
    }
  }

  def declarationDef(): ExportFileCommand = {
    next() match {
      case 'A' =>
        consume('X')
        val n = spc(nameRef())
        val t = spc(exprRef())
        val ups = univParams()
        ExportedModification(AxiomMod(n, ups, t))
      case 'D' =>
        consume('E'); consume('F')
        val n = spc(nameRef())
        val t = spc(exprRef())
        val v = spc(exprRef())
        val hints = spc(hintsDef())
        val ups = univParams()
        ExportedModification(DefMod(n, ups, t, v, hints))
      case 'T' =>
        consume('H'); consume('M')
        val n = spc(nameRef())
        val t = spc(exprRef())
        val v = spc(exprRef())
        val ups = univParams()
        ExportedModification(TheoremMod(n, ups, t, v))
      case 'O' =>
        consume('P'); consume('A'); consume('Q')
        val n = spc(nameRef())
        val t = spc(exprRef())
        val v = spc(exprRef())
        val ups = univParams()
        ExportedModification(OpaqueMod(n, ups, t, v))
      case 'Q' =>
        consume("UOT")
        val n = spc(nameRef())
        val t = spc(exprRef())
        // Format: #QUOT name type univParams... [kind]
        // univParams are name references, kind (if present) is a large number (100/200/300)
        val ups = univParams()
        // Each #QUOT is a separate builtin axiom declaration
        ExportedModification(AxiomMod(n, ups, t))
      case 'I' =>
        next() match {
          case 'N' =>
            next() match {
              case 'D' =>
                // Lean 4 inductive: #IND name type isRefl isRec numNested numParams numIndices numInds indNames... numCtors ctorNames... uparams...
                val n = spc(nameRef())
                val t = spc(exprRef())
                val isReflexive = spc(num()) != 0
                val isRecursive = spc(num()) != 0
                val numNested = spc(num())
                val numParams = spc(num())
                val numIndices = spc(num())
                val numInds = spc(num())
                val indNames = (0 until numInds).map(_ => spc(nameRef())).toVector
                val numCtors = spc(num())
                val ctorNames = (0 until numCtors).map(_ => spc(nameRef())).toVector
                val ups = univParams()
                // For now, create a simplified IndMod - the constructors come separately via #CTOR
                ExportedModification(IndMod(n, ups, t, numParams, ctorNames.map(cn => (cn, Sort.Prop))))
              case 'F' =>
                // Legacy notation: #INFIX (keep for compatibility)
                consume("IX ")
                ExportedNotation(Infix(nameRef(), spc(num()), spc(rest())))
            }
          case _ => throw new IllegalArgumentException(s"Unknown command starting with #I")
        }
      case 'C' =>
        consume('T'); consume('O'); consume('R')
        val n = spc(nameRef())
        val t = spc(exprRef())
        val inductName = spc(nameRef())
        val cidx = spc(num())
        val numParams = spc(num())
        val numFields = spc(num())
        val ups = univParams()
        ExportedModification(CtorMod(n, ups, t, inductName, cidx, numParams, numFields))
      case 'R' =>
        consume('E'); consume('C')
        val n = spc(nameRef())
        val t = spc(exprRef())
        val numInds = spc(num())
        val indNames = (0 until numInds).map(_ => spc(nameRef())).toVector
        val numParams = spc(num())
        val numIndices = spc(num())
        val numMotives = spc(num())
        val numMinors = spc(num())
        val numRules = spc(num())
        val ruleIdxs = (0 until numRules).map(_ => spc(num())).toVector
        val isK = spc(num()) != 0
        val ups = univParams()
        val rules = ruleIdxs.map(recRule(_))
        ExportedModification(RecursorMod(n, ups, t, indNames, numParams, numIndices, numMotives, numMinors, recRules = rules, isK))
      case 'P' =>
        // Legacy notation commands
        next() match {
          case 'R' =>
            consume("EFIX ")
            ExportedNotation(Prefix(nameRef(), spc(num()), spc(rest())))
          case 'O' =>
            consume("STFIX ")
            ExportedNotation(Postfix(nameRef(), spc(num()), spc(rest())))
        }
    }
  }

  def hintsDef(): ReducibilityHints =
    next() match {
      case 'O' => ReducibilityHints.Opaque
      case 'A' => ReducibilityHints.Abbrev
      case 'R' => ReducibilityHints.Regular(spc(num()))
    }

  def num(): Int = long().toInt
  def long(): Long =
    next() match { case c if '0' <= c && c <= '9' => long(c - '0') }
  def long(acc: Long): Long =
    cur() match {
      case c if '0' <= c && c <= '9' =>
        next()
        long(10 * acc + (c - '0'))
      case _ => acc
    }

  def rest(): String = {
    val start = index
    def nextNL(): Int = if (cur() == '\n') index else { next(); nextNL() }
    new String(bytes, start, math.max(nextNL() - start, 0), LinesParser.UTF8)
  }

  def nameRef(): Name = name(num())

  def levelRef(): Level = level(num())
  def levelDef(): Level =
    next() match {
      case 'Z' => Level.Zero  // Universe zero
      case 'S' => Level.Succ(spc(levelRef()))
      case 'M' => Level.Max(spc(levelRef()), spc(levelRef()))
      case 'I' => consume('M'); Level.IMax(spc(levelRef()), spc(levelRef()))
      case 'P' => Level.Param(spc(nameRef()))
    }

  @inline def restOf[T](p: => T): Vector[T] = {
    val out = Vector.newBuilder[T]
    while (cur() == ' ') {
      // Skip all consecutive spaces
      while (cur() == ' ') next()
      // Check if there's actually content (not just newline)
      if (cur() >= '0' && cur() <= '9') {
        out += p
      } else {
        // Newline or non-digit - stop parsing
        return out.result()
      }
    }
    out.result()
  }

  def binderInfo(): BinderInfo = {
    consume('#'); consume('B')
    next() match {
      case 'D' => BinderInfo.Default
      case 'I' => BinderInfo.Implicit
      case 'C' => BinderInfo.InstImplicit
      case 'S' => BinderInfo.StrictImplicit
    }
  }

  @inline def c[T](c: Char, p: => T): T = { consume(c); p }
  @inline def spc[T](p: => T): T = {
    // Require at least one space, then skip any additional spaces
    consume(' ')
    while (cur() == ' ') next()
    p
  }

  def exprRef(): Expr = expr(num())
  def exprDef(): Expr =
    next() match {
      case 'V' =>
        Var(spc(num()))
      case 'S' =>
        Sort(spc(levelRef()))
      case 'C' =>
        Const(spc(nameRef()), restOf(levelRef()))
      case 'A' =>
        App(spc(exprRef()), spc(exprRef()))
      case 'L' =>
        // Lambda: #EL info name domain body
        val b = spc(binderInfo())
        val n = spc(nameRef())
        val d = spc(exprRef())
        val e = spc(exprRef())
        Lam(Binding(n, d, b), e)
      case 'P' =>
        // Pi: #EP info name domain body
        val b = spc(binderInfo())
        val n = spc(nameRef())
        val d = spc(exprRef())
        val e = spc(exprRef())
        Pi(Binding(n, d, b), e)
      case 'Z' =>
        // Let: #EZ name type value body
        val n = spc(nameRef())
        val t = spc(exprRef())
        val v = spc(exprRef())
        val e = spc(exprRef())
        Let(Binding(n, t, BinderInfo.Default), v, e)
      case 'J' =>
        // Projection: #EJ typeName idx struct
        val typeName = spc(nameRef())
        val idx = spc(num())
        val struct = spc(exprRef())
        Proj(typeName, idx, struct)
    }

  // Handle ELN and ELS separately since they start with EL
  def exprDefExtended(): Expr = {
    val firstChar = next()
    firstChar match {
      case 'V' => Var(spc(num()))
      case 'S' => Sort(spc(levelRef()))
      case 'C' => Const(spc(nameRef()), restOf(levelRef()))
      case 'A' => App(spc(exprRef()), spc(exprRef()))
      case 'L' =>
        // Could be #EL (lambda) or #ELN (nat lit) or #ELS (string lit)
        peek() match {
          case 'N' =>
            // Nat literal: #ELN value
            consume('N')
            NatLit(BigInt(spc(rest())))
          case 'S' =>
            // String literal: #ELS hexbytes
            consume('S')
            val hexStr = spc(rest())
            val bytes = hexStr.split(" ").filter(_.nonEmpty).map(h => Integer.parseInt(h, 16).toByte)
            StringLit(new String(bytes, LinesParser.UTF8))
          case _ =>
            // Lambda: #EL info name domain body
            val b = spc(binderInfo())
            val n = spc(nameRef())
            val d = spc(exprRef())
            val e = spc(exprRef())
            Lam(Binding(n, d, b), e)
        }
      case 'P' =>
        val b = spc(binderInfo())
        val n = spc(nameRef())
        val d = spc(exprRef())
        val e = spc(exprRef())
        Pi(Binding(n, d, b), e)
      case 'Z' =>
        val n = spc(nameRef())
        val t = spc(exprRef())
        val v = spc(exprRef())
        val e = spc(exprRef())
        Let(Binding(n, t, BinderInfo.Default), v, e)
      case 'J' =>
        val typeName = spc(nameRef())
        val idx = spc(num())
        val struct = spc(exprRef())
        Proj(typeName, idx, struct)
      case other =>
        throw new IllegalArgumentException(s"Unknown expression type: E$other")
    }
  }

  def univParams(): Vector[Level.Param] =
    restOf(Level.Param(nameRef()))
}

object LinesParser {
  val UTF8: Charset = Charset.forName("UTF-8")
}

// Override exprDef to use the extended version
private final class Lean4LinesParser(textExportParser: TextExportParser, bytes: Array[Byte], end: Int)
    extends LinesParser(textExportParser, bytes, end) {

  override def exprDef(): Expr = exprDefExtended()
}

object TextExportParser {
  @tailrec private def reverseIndexOf(chunk: Array[Byte], needle: Byte, from: Int): Int =
    if (chunk(from) == needle) from
    else if (from == 0) -1
    else reverseIndexOf(chunk, needle, from - 1)

  def parseStream(in: InputStream): LazyList[ExportFileCommand] = {
    def bufSize = 8 << 10
    case class Chunk(bytes: Array[Byte], endIndex: Int)
    def readChunksCore(buf: Array[Byte], begin: Int): LazyList[Chunk] = {
      val len = in.read(buf, begin, buf.length - begin)
      if (len <= 0) LazyList.empty else {
        val nl = reverseIndexOf(buf, '\n', begin + len - 1)
        if (nl == -1) {
          // no newline found in the whole chunk,
          // this should only happen at the end but let's try again to make sure
          Chunk(buf, len) #:: readChunks()
        } else {
          val nextBuf = new Array[Byte](bufSize)
          val reuse = (begin + len) - (nl + 1)
          System.arraycopy(buf, nl + 1, nextBuf, 0, reuse)
          Chunk(buf, nl + 1) #:: readChunksCore(nextBuf, reuse)
        }
      }
    }
    def readChunks(): LazyList[Chunk] = readChunksCore(new Array[Byte](bufSize), 0)
    val parser = new TextExportParser
    readChunks().flatMap(chunk => new Lean4LinesParser(parser, chunk.bytes, chunk.endIndex).lines())
  }

  def parseFile(fn: String): LazyList[ExportFileCommand] = parseStream(new FileInputStream(fn))
}
