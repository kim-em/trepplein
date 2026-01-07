package trepplein

import java.util.function.Predicate

import trepplein.Level._

import scala.annotation.tailrec
import scala.collection.mutable

sealed abstract class BinderInfo extends Product {
  def dump = s"BinderInfo.$productPrefix"
}
object BinderInfo {
  case object Default extends BinderInfo
  case object Implicit extends BinderInfo
  case object StrictImplicit extends BinderInfo
  case object InstImplicit extends BinderInfo
}

case class Binding(prettyName: Name, ty: Expr, info: BinderInfo) {
  def dump(implicit lcs: mutable.Map[LocalConst.Name, String]) =
    s"Binding(${prettyName.dump}, ${ty.dump}, ${info.dump})"

  override val hashCode: Int = prettyName.hashCode + 37 * (ty.hashCode + 37 * info.hashCode)

  def equalsCore(that: Binding)(implicit cache: ExprEqCache): Boolean =
    this.info == that.info &&
      this.ty.equalsCore(that.ty) &&
      this.prettyName == that.prettyName
}

private class ExprCache extends java.util.IdentityHashMap[Expr, Expr] {
  @inline final def getOrElseUpdate(k: Expr)(v: Expr => Expr): Expr = {
    val cached = get(k)
    if (cached != null) {
      cached
    } else {
      val computed = v(k)
      put(k, computed)
      computed
    }
  }
}
private class ExprOffCache extends mutable.ArrayBuffer[ExprCache] {
  @inline final def getOrElseUpdate(k: Expr, off: Int)(v: Expr => Expr): Expr = {
    while (off >= size) this += new ExprCache
    this(off).getOrElseUpdate(k)(v)
  }
}

private class ExprEqCache extends java.util.IdentityHashMap[Expr, UFNode] {
  // Only find existing UFNode, don't create new one
  @inline private def findExisting(e: Expr): UFNode = {
    val n = get(e)
    if (n == null) null
    else n.find()
  }

  // Get or create UFNode - only call when we're about to union
  @inline private def getOrCreate(e: Expr): UFNode = {
    var n = get(e)
    if (n == null) {
      n = new UFNode
      put(e, n)
      n
    } else {
      n.find()
    }
  }

  @inline final def checkAndThenUnion(a: Expr, b: Expr)(v: (Expr, Expr) => Boolean): Boolean = {
    // Fast path: check if already in same equivalence class without creating nodes
    val aNode = findExisting(a)
    val bNode = findExisting(b)
    if (aNode != null && bNode != null && (aNode eq bNode)) return true

    // Slow path: actually compare and potentially union
    if (v(a, b)) {
      // Only create UFNodes when expressions are equal
      getOrCreate(a).union(getOrCreate(b))
      true
    } else {
      false
    }
  }
}

private object Breadcrumb

sealed abstract class Expr(val varBound: Int, val hasLocals: Boolean, override val hashCode: Int) extends Product {
  final def hasVar(i: Int): Boolean =
    this match {
      case _ if varBound <= i => false
      case Var(idx) => idx == i
      case App(a, b) => a.hasVar(i) || b.hasVar(i)
      case Lam(dom, body) => dom.ty.hasVar(i) || body.hasVar(i + 1)
      case Pi(dom, body) => dom.ty.hasVar(i) || body.hasVar(i + 1)
      case Let(dom, value, body) => dom.ty.hasVar(i) || value.hasVar(i) || body.hasVar(i + 1)
      case Proj(_, _, struct) => struct.hasVar(i)
      case _: NatLit | _: StringLit => false
    }

  def hasVars: Boolean = varBound > 0

  override def equals(that: Any): Boolean =
    that match {
      case that: Expr => equals(that)
      case _ => false
    }
  def equals(that: Expr): Boolean = equalsCore(that)(new ExprEqCache)
  def equalsCore(that: Expr)(implicit cache: ExprEqCache): Boolean =
    (this eq that) || this.hashCode == that.hashCode &&
      cache.checkAndThenUnion(this, that) {
        case (Var(i1), Var(i2)) => i1 == i2
        case (Sort(l1), Sort(l2)) => l1 == l2
        case (Const(n1, l1), Const(n2, l2)) => n1 == n2 && l1 == l2
        case (LocalConst(_, n1), LocalConst(_, n2)) => n1 == n2
        case (App(a1, b1), App(a2, b2)) => a1.equalsCore(a2) && b1.equalsCore(b2)
        case (Lam(d1, b1), Lam(d2, b2)) => d1.equalsCore(d2) && b1.equalsCore(b2)
        case (Pi(d1, b1), Pi(d2, b2)) => d1.equalsCore(d2) && b1.equalsCore(b2)
        case (Let(d1, v1, b1), Let(d2, v2, b2)) => d1.equalsCore(d2) && v1.equalsCore(v2) && b1.equalsCore(b2)
        case (Proj(t1, i1, s1), Proj(t2, i2, s2)) => t1 == t2 && i1 == i2 && s1.equalsCore(s2)
        case (NatLit(n1), NatLit(n2)) => n1 == n2
        case (StringLit(s1), StringLit(s2)) => s1 == s2
        case _ => false
      }

  def abstr(lc: LocalConst): Expr = abstr(0, Vector(lc))
  def abstr(off: Int, lcs: Vector[LocalConst]): Expr =
    abstrCore(off, lcs)(new ExprOffCache)
  private def abstrCore(off: Int, lcs: Vector[LocalConst])(implicit cache: ExprOffCache): Expr =
    cache.getOrElseUpdate(this, off) {
      case _ if !hasLocals => this
      case LocalConst(_, name) =>
        lcs.indexWhere(_.name == name) match {
          case -1 => this
          case i => Var(i + off)
        }
      case App(a, b) =>
        App(a.abstrCore(off, lcs), b.abstrCore(off, lcs))
      case Lam(domain, body) =>
        Lam(domain.copy(ty = domain.ty.abstrCore(off, lcs)), body.abstrCore(off + 1, lcs))
      case Pi(domain, body) =>
        Pi(domain.copy(ty = domain.ty.abstrCore(off, lcs)), body.abstrCore(off + 1, lcs))
      case Let(domain, value, body) =>
        Let(domain.copy(ty = domain.ty.abstrCore(off, lcs)), value.abstrCore(off, lcs), body.abstrCore(off + 1, lcs))
      case Proj(typeName, idx, struct) =>
        Proj(typeName, idx, struct.abstrCore(off, lcs))
      case _: NatLit | _: StringLit => this
    }

  def instantiate(e: Expr): Expr = instantiate(0, Vector(e))
  def instantiate(off: Int, es: Vector[Expr]): Expr =
    if (varBound <= off) this else
      instantiateIterative(off, es)

  /** Iterative implementation of instantiate to avoid stack overflow on deeply nested expressions.
   *  Uses an explicit worklist instead of recursion.
   *
   *  Optimized to minimize allocations:
   *  - Uses parallel arrays instead of case class work items
   *  - Uses stack index for results instead of removing elements
   *  - Uses single-level cache with packed key
   */
  private def instantiateIterative(startOff: Int, es: Vector[Expr]): Expr = {
    // Single-level cache using (expr, off) -> result
    // Key is the expression itself (identity), value is (off -> result) stored inline
    // For most cases off is small (< 100), so we use a simple approach
    val cache = new java.util.IdentityHashMap[Expr, AnyRef]()
    // Cache entries: either Expr (for off=0) or Array[Expr] indexed by off

    // Worklist as parallel arrays - avoids allocating WorkItem objects
    // Each entry at index i has: workExprs(i), workOffs(i), workContIdx(i)
    var workExprs = new Array[Expr](256)
    var workOffs = new Array[Int](256)
    var workContIdx = new Array[Int](256)
    var workSize = 0

    // Results stack - we track the top instead of removing elements
    var resultStack = new Array[Expr](256)
    var resultTop = 0

    // Push initial work item
    workExprs(0) = this
    workOffs(0) = startOff
    workContIdx(0) = -1
    workSize = 1

    // Helper to grow arrays if needed
    def growWork(): Unit = {
      val newSize = workExprs.length * 2
      workExprs = java.util.Arrays.copyOf(workExprs, newSize)
      workOffs = java.util.Arrays.copyOf(workOffs, newSize)
      workContIdx = java.util.Arrays.copyOf(workContIdx, newSize)
    }
    def growResults(): Unit = {
      resultStack = java.util.Arrays.copyOf(resultStack, resultStack.length * 2)
    }

    // Push work item
    @inline def pushWork(expr: Expr, off: Int, cont: Int): Unit = {
      if (workSize >= workExprs.length) growWork()
      workExprs(workSize) = expr
      workOffs(workSize) = off
      workContIdx(workSize) = cont
      workSize += 1
    }

    // Push result
    @inline def pushResult(r: Expr): Unit = {
      if (resultTop >= resultStack.length) growResults()
      resultStack(resultTop) = r
      resultTop += 1
    }

    // Cache operations - use array for all entries to avoid type confusion
    @inline def cacheGet(expr: Expr, off: Int): Expr = {
      val entry = cache.get(expr)
      if (entry == null) null
      else {
        val arr = entry.asInstanceOf[Array[Expr]]
        if (off < arr.length) arr(off) else null
      }
    }

    @inline def cachePut(expr: Expr, off: Int, result: Expr): Unit = {
      val entry = cache.get(expr)
      if (entry == null) {
        val arr = new Array[Expr](math.max(off + 1, 4))  // Start with size 4 to reduce resizing
        arr(off) = result
        cache.put(expr, arr)
      } else {
        val arr = entry.asInstanceOf[Array[Expr]]
        if (off < arr.length) {
          arr(off) = result
        } else {
          val newArr = java.util.Arrays.copyOf(arr, math.max(off + 1, arr.length * 2))
          newArr(off) = result
          cache.put(expr, newArr)
        }
      }
    }

    while (workSize > 0) {
      workSize -= 1
      val expr = workExprs(workSize)
      val off = workOffs(workSize)
      val contIdx = workContIdx(workSize)

      // Check cache first
      val cached = cacheGet(expr, off)
      if (cached != null) {
        pushResult(cached)
      } else if (expr.varBound <= off) {
        // No variables to substitute at this offset
        cachePut(expr, off, expr)
        pushResult(expr)
      } else {
        expr match {
          case Var(idx) =>
            val result = if (off <= idx && idx < off + es.size) es(idx - off) else expr
            cachePut(expr, off, result)
            pushResult(result)

          case App(a, b) =>
            if (contIdx == -1) {
              // First time - push continuation and children
              pushWork(expr, off, resultTop)  // Continuation with current result position
              pushWork(b, off, -1)
              pushWork(a, off, -1)
            } else {
              // Continuation - results are at contIdx and contIdx+1
              val aResult = resultStack(contIdx)
              val bResult = resultStack(contIdx + 1)
              resultTop = contIdx  // Pop the child results
              val result = if ((aResult eq a) && (bResult eq b)) expr else App(aResult, bResult)
              cachePut(expr, off, result)
              pushResult(result)
            }

          case Lam(domain, body) =>
            if (contIdx == -1) {
              pushWork(expr, off, resultTop)
              pushWork(body, off + 1, -1)
              pushWork(domain.ty, off, -1)
            } else {
              val tyResult = resultStack(contIdx)
              val bodyResult = resultStack(contIdx + 1)
              resultTop = contIdx
              val newDomain = if (tyResult eq domain.ty) domain else domain.copy(ty = tyResult)
              val result = if ((newDomain eq domain) && (bodyResult eq body)) expr else Lam(newDomain, bodyResult)
              cachePut(expr, off, result)
              pushResult(result)
            }

          case Pi(domain, body) =>
            if (contIdx == -1) {
              pushWork(expr, off, resultTop)
              pushWork(body, off + 1, -1)
              pushWork(domain.ty, off, -1)
            } else {
              val tyResult = resultStack(contIdx)
              val bodyResult = resultStack(contIdx + 1)
              resultTop = contIdx
              val newDomain = if (tyResult eq domain.ty) domain else domain.copy(ty = tyResult)
              val result = if ((newDomain eq domain) && (bodyResult eq body)) expr else Pi(newDomain, bodyResult)
              cachePut(expr, off, result)
              pushResult(result)
            }

          case Let(domain, value, body) =>
            if (contIdx == -1) {
              pushWork(expr, off, resultTop)
              pushWork(body, off + 1, -1)
              pushWork(value, off, -1)
              pushWork(domain.ty, off, -1)
            } else {
              val tyResult = resultStack(contIdx)
              val valueResult = resultStack(contIdx + 1)
              val bodyResult = resultStack(contIdx + 2)
              resultTop = contIdx
              val newDomain = if (tyResult eq domain.ty) domain else domain.copy(ty = tyResult)
              val result = if ((newDomain eq domain) && (valueResult eq value) && (bodyResult eq body))
                expr
              else
                Let(newDomain, valueResult, bodyResult)
              cachePut(expr, off, result)
              pushResult(result)
            }

          case Proj(typeName, idx, struct) =>
            if (contIdx == -1) {
              pushWork(expr, off, resultTop)
              pushWork(struct, off, -1)
            } else {
              val structResult = resultStack(contIdx)
              resultTop = contIdx
              val result = if (structResult eq struct) expr else Proj(typeName, idx, structResult)
              cachePut(expr, off, result)
              pushResult(result)
            }

          case _: NatLit | _: StringLit | _: Sort | _: Const | _: LocalConst =>
            cachePut(expr, off, expr)
            pushResult(expr)
        }
      }
    }

    resultStack(0)
  }

  def instantiate(subst: Map[Param, Level]): Expr =
    if (subst.forall(x => x._1 == x._2)) this else instantiateCore(subst)(new ExprCache)
  private def instantiateCore(subst: Map[Param, Level])(implicit cache: ExprCache): Expr =
    cache.getOrElseUpdate(this) {
      case v: Var => v
      case Sort(level) => Sort(level.instantiate(subst))
      case Const(name, levels) => Const(name, levels.map(_.instantiate(subst)))
      case LocalConst(of, name) => LocalConst(of.copy(ty = of.ty.instantiateCore(subst)), name)
      case App(a, b) => App(a.instantiateCore(subst), b.instantiateCore(subst))
      case Lam(domain, body) => Lam(domain.copy(ty = domain.ty.instantiateCore(subst)), body.instantiateCore(subst))
      case Pi(domain, body) => Pi(domain.copy(ty = domain.ty.instantiateCore(subst)), body.instantiateCore(subst))
      case Let(domain, value, body) => Let(
        domain.copy(ty = domain.ty.instantiateCore(subst)),
        value.instantiateCore(subst), body.instantiateCore(subst))
      case Proj(typeName, idx, struct) => Proj(typeName, idx, struct.instantiateCore(subst))
      case lit: NatLit => lit
      case lit: StringLit => lit
    }

  final def foreach_(f: Predicate[Expr]): Unit =
    if (f.test(this)) this match {
      case App(a, b) =>
        a.foreach_(f)
        b.foreach_(f)
      case Lam(domain, body) =>
        domain.ty.foreach_(f)
        body.foreach_(f)
      case Pi(domain, body) =>
        domain.ty.foreach_(f)
        body.foreach_(f)
      case Let(domain, value, body) =>
        domain.ty.foreach_(f)
        value.foreach_(f)
        body.foreach_(f)
      case Proj(_, _, struct) =>
        struct.foreach_(f)
      case _: Var | _: Const | _: Sort | _: LocalConst | _: NatLit | _: StringLit =>
    }

  @inline final def foreachNoDups(f: Expr => Unit): Unit = {
    val seen = new java.util.IdentityHashMap[Expr, Breadcrumb.type]()
    foreach_ { x =>
      if (seen.put(x, Breadcrumb) == null) {
        f(x)
        true
      } else {
        false
      }
    }
  }

  @inline private def buildSet[T](f: mutable.Set[T] => Unit): Set[T] = {
    val set = mutable.Set[T]()
    f(set)
    set.toSet
  }

  def univParams: Set[Param] =
    buildSet { ps =>
      foreachNoDups {
        case Sort(level) => ps ++= level.univParams
        case Const(_, levels) => ps ++= levels.view.flatMap(_.univParams)
        case _ =>
      }
    }

  def constants: Set[Name] =
    buildSet { cs =>
      foreachNoDups {
        case Const(name, _) => cs += name
        case Proj(typeName, _, _) => cs += typeName
        case _ =>
      }
    }

  def -->:(that: Expr): Expr =
    Pi(Binding(Name.Anon, that, BinderInfo.Default), this)

  override def toString: String = pretty(this)

  def dump(implicit lcs: mutable.Map[LocalConst.Name, String] = null): String =
    this match {
      case _ if lcs eq null =>
        val lcs_ = mutable.Map[LocalConst.Name, String]()
        val d = dump(lcs_)
        if (lcs_.isEmpty) d else {
          val decls = lcs.values.map { n => s"val $n = new LocalConst.Name()\n" }.mkString
          s"{$decls$d}"
        }
      case Var(i) => s"Var($i)"
      case Sort(level) => s"Sort(${level.dump})"
      case Const(name, levels) => s"Const(${name.dump}, Vector(${levels.map(_.dump).mkString(", ")}))"
      case App(a, b) => s"App(${a.dump}, ${b.dump})"
      case Lam(dom, body) => s"Lam(${dom.dump}, ${body.dump})"
      case Pi(dom, body) => s"Pi(${dom.dump}, ${body.dump})"
      case LocalConst(of, name) =>
        val of1 = of.prettyName.toString.replace('.', '_').filter { _.isLetterOrDigit }
        val of2 = if (of1.isEmpty || !of1.head.isLetter) s"n$of1" else of1
        val n = lcs.getOrElseUpdate(name, LazyList.from(0).map(i => s"$of2$i").diff(lcs.values.toSeq).head)
        s"LocalConst(${of.dump}, $n)"
      case Let(dom, value, body) => s"Let(${dom.dump}, ${value.dump}, ${body.dump})"
      case Proj(typeName, idx, struct) => s"Proj(${typeName.dump}, $idx, ${struct.dump})"
      case NatLit(n) => s"NatLit($n)"
      case StringLit(s) => s"""StringLit("${s.replace("\"", "\\\"")}")"""
    }
}
case class Var(idx: Int) extends Expr(varBound = idx + 1, hasLocals = false, hashCode = idx)
case class Sort(level: Level) extends Expr(varBound = 0, hasLocals = false, hashCode = level.hashCode)

case class Const(name: Name, levels: Vector[Level])
  extends Expr(varBound = 0, hasLocals = false, hashCode = 37 * name.hashCode)
case class LocalConst(of: Binding, name: LocalConst.Name = new LocalConst.Name)
  extends Expr(varBound = 0, hasLocals = true, hashCode = 4 + name.hashCode)
case class App(a: Expr, b: Expr)
  extends Expr(
    varBound = math.max(a.varBound, b.varBound),
    hasLocals = a.hasLocals || b.hasLocals,
    hashCode = a.hashCode + 37 * b.hashCode)
case class Lam(domain: Binding, body: Expr)
  extends Expr(
    varBound = math.max(domain.ty.varBound, body.varBound - 1),
    hasLocals = domain.ty.hasLocals || body.hasLocals,
    hashCode = 1 + 37 * domain.hashCode + body.hashCode)
case class Pi(domain: Binding, body: Expr)
  extends Expr(
    varBound = math.max(domain.ty.varBound, body.varBound - 1),
    hasLocals = domain.ty.hasLocals || body.hasLocals,
    hashCode = 2 + 37 * domain.hashCode + body.hashCode)
case class Let(domain: Binding, value: Expr, body: Expr)
  extends Expr(
    varBound = math.max(math.max(domain.ty.varBound, value.varBound), body.varBound - 1),
    hasLocals = domain.ty.hasLocals || value.hasLocals || body.hasLocals,
    hashCode = 3 + 37 * (domain.hashCode + 37 * value.hashCode) + body.hashCode)

// Lean 4 expression types
case class Proj(typeName: Name, idx: Int, struct: Expr)
  extends Expr(
    varBound = struct.varBound,
    hasLocals = struct.hasLocals,
    hashCode = 5 + typeName.hashCode + 37 * (idx + 37 * struct.hashCode))

case class NatLit(value: BigInt)
  extends Expr(varBound = 0, hasLocals = false, hashCode = 6 + value.hashCode)

case class StringLit(value: String)
  extends Expr(varBound = 0, hasLocals = false, hashCode = 7 + value.hashCode)

object Sort {
  val Prop = Sort(Level.Zero)
}

object LocalConst {
  final class Name {
    override def toString: String = Integer.toHexString(hashCode()).take(4)
  }
}

trait Binder[T] {
  def apply(domain: Binding, body: Expr): T
  def apply(domain: LocalConst, body: Expr): T =
    apply(domain.of, body.abstr(domain))

  trait GenericUnapply {
    def unapply(e: Expr): Option[(Binding, Expr)]
  }
  val generic: GenericUnapply
}

trait Binders[T <: Expr] {
  protected val Single: Binder[T]

  def apply(domains: Iterable[LocalConst])(body: Expr): Expr =
    domains.foldRight(body)(Single.apply)

  def apply(domains: LocalConst*)(body: Expr): Expr =
    apply(domains)(body)

  def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
    e match {
      case Single.generic(dom, expr) =>
        val lc = LocalConst(dom)
        unapply(expr.instantiate(lc)) match {
          case Some((lcs, head)) =>
            Some((lc :: lcs, head))
        }
      case _ => Some((Nil, e))
    }
}

object Let {
  def apply(x: LocalConst, v: Expr, b: Expr): Let =
    Let(x.of, v, b.abstr(x))
}

object Lam extends Binder[Lam] {
  val generic: GenericUnapply = {
    case e: Lam => Some((e.domain, e.body))
    case _ => None
  }
}
object Lams extends Binders[Lam] {
  protected val Single = Lam
}

object Pi extends Binder[Pi] {
  val generic: GenericUnapply = {
    case e: Pi => Some((e.domain, e.body))
    case _ => None
  }
}
object Pis extends Binders[Pi] {
  protected val Single = Pi
}

object Apps {
  @tailrec
  private def decompose(e: Expr, as: List[Expr] = Nil): (Expr, List[Expr]) =
    e match {
      case App(f, a) => decompose(f, a :: as)
      case _ => (e, as)
    }

  def unapply(e: Expr): Some[(Expr, List[Expr])] =
    Some(decompose(e))

  def apply(fn: Expr, as: Iterable[Expr]): Expr =
    as.foldLeft(fn)(App)

  def apply(fn: Expr, as: Expr*): Expr =
    apply(fn, as)
}
