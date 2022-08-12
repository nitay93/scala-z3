package nitaii.z3.solver

import com.microsoft.z3._

object Z3Utils {
  val ctx = new Context

  def newSolver: Solver = ctx.mkSolver()

  implicit def intToWrapper(i: Int): NumWrapper = new NumWrapper(ctx.mkInt(i))

  implicit def intToExpr(i: Int): IntNum = ctx.mkInt(i)

  implicit def boolToWrapper(b: Boolean): BoolWrapper = new BoolWrapper(ctx.mkBool(b))

  implicit def boolToExpr(b: Boolean): BoolExpr = ctx.mkBool(b)

  implicit def realToWrapper(d: Double): NumWrapper = new NumWrapper(ctx.mkReal(d.toString()))

  implicit def realToExpr(d: Double): RatNum = ctx.mkReal(d.toString())

  implicit def boolWrapperToExpr(wrapper: BoolWrapper): BoolExpr = wrapper.e

  implicit def numWrapperToExpr(wrapper: NumWrapper): ArithExpr[_ <: ArithSort] = wrapper.e

  implicit def intWrapperToExpr(wrapper: IntWrapper): IntExpr = wrapper.e.asInstanceOf[IntExpr]

  //  implicit def wrapperToExpr(wrapper : ExprWrapper) : Expr[_ <: Sort] = wrapper.expr

  implicit def boolWrappersToExpr(boolExps: Seq[BoolWrapper]): Seq[BoolExpr] =
    boolExps.map { boolExp => boolExp.e }

  implicit def numWrappersToExpr[T <: ArithExpr[_ <: ArithSort]](numExps: Seq[NumWrapper]): Seq[ArithExpr[_ <: ArithSort]] =
    numExps.map { NumWrapper => NumWrapper.e }

  implicit def WrapperToExpr(wrapper: ExprWrapper): Expr[_ <: Sort] = wrapper.expr

  implicit def ExprToWrapper(expr: Expr[_ <: Sort]): ExprWrapper = new ExprWrapper(expr)

  //  implicit def

  class ExprWrapper(val expr: Expr[_ <: Sort]) {
    def ~=(otherExpr: Expr[_ <: Sort]): BoolExpr = ctx.mkEq(expr, otherExpr)
  }

  case class B(symbol: String) extends BoolWrapper(ctx.mkBoolConst(symbol))

  implicit class BoolWrapper(val e: BoolExpr) extends ExprWrapper(e) {
    def |(otherExpr: BoolWrapper): BoolExpr =
      ctx.mkOr(e, otherExpr)

    def &(otherExpr: BoolWrapper): BoolExpr =
      ctx.mkAnd(e, otherExpr)

    def ->(otherExpr: BoolWrapper): BoolExpr =
      ctx.mkImplies(e, otherExpr)

    def <->(otherExpr: BoolWrapper): BoolExpr = ~=(otherExpr)
  }

  /**
   * integer variables
   */
  case class Z(symbol: String) extends IntWrapper(ctx.mkIntConst(symbol))

  /**
   * real variables
   */
  case class R(symbol: String) extends RealWrapper(ctx.mkRealConst(symbol))

  implicit class IntWrapper(int: IntExpr) extends NumWrapper(int) {
    def +(otherNE: IntExpr): IntExpr = ctx.mkAdd(e, otherNE).asInstanceOf[IntExpr]
    //    def +(otherNE: RealExpr): RealExpr = ctx.mkAdd(e, otherNE).asInstanceOf[RealExpr]

    def -(otherNE: IntExpr): IntExpr = ctx.mkSub(e, otherNE).asInstanceOf[IntExpr]

    def -(otherNE: RealExpr): RealExpr = ctx.mkSub(e, otherNE).asInstanceOf[RealExpr]

    def *(otherNE: IntExpr): IntExpr = ctx.mkMul(e, otherNE).asInstanceOf[IntExpr]

    def *(otherNE: RealExpr): RealExpr = ctx.mkMul(e, otherNE).asInstanceOf[RealExpr]

    def /(otherNE: RealExpr): RealExpr = ctx.mkDiv(e, otherNE).asInstanceOf[RealExpr]

    def /(otherNE: IntExpr): IntExpr = ctx.mkDiv(e, otherNE).asInstanceOf[IntExpr]

  }

  implicit class RealWrapper(real: RealExpr) extends NumWrapper(real) {
    def +(otherNE: IntExpr): RealExpr = ctx.mkAdd(e, otherNE).asInstanceOf[RealExpr]

    def +(otherNE: RealExpr): RealExpr = ctx.mkAdd(e, otherNE).asInstanceOf[RealExpr]

    def -(otherNE: IntExpr): RealExpr = ctx.mkSub(e, otherNE).asInstanceOf[RealExpr]

    def -(otherNE: RealExpr): RealExpr = ctx.mkSub(e, otherNE).asInstanceOf[RealExpr]

    def *(otherNE: IntExpr): RealExpr = ctx.mkMul(e, otherNE).asInstanceOf[RealExpr]

    def *(otherNE: RealExpr): RealExpr = ctx.mkMul(e, otherNE).asInstanceOf[RealExpr]

    def /(otherNE: RealExpr): RealExpr = ctx.mkDiv(e, otherNE).asInstanceOf[RealExpr]

    def /(otherNE: IntExpr): IntExpr = ctx.mkDiv(e, otherNE).asInstanceOf[IntExpr]
    //    def /(i : Int) = ctx.mkDiv(e, i).asInstanceOf[IntExpr]
  }


  implicit class NumWrapper(val e: ArithExpr[_ <: ArithSort]) extends ExprWrapper(e) {
    def <=[E <: ArithExpr[_ <: ArithSort]](otherNE: NumWrapper): BoolExpr = ctx.mkLe(e, otherNE.e)

    def <[E <: ArithExpr[_ <: ArithSort]](otherNE: NumWrapper): BoolExpr = ctx.mkLt(e, otherNE.e)

    def >=[E <: ArithExpr[_ <: ArithSort]](otherNE: NumWrapper): BoolExpr = ctx.mkGe(e, otherNE.e)

    def >[E <: ArithExpr[_ <: ArithSort]](otherNE: NumWrapper): BoolExpr = ctx.mkGt(e, otherNE.e)
  }

  def sum(numExps: ArithExpr[_ <: ArithSort]*): ArithExpr[_ <: ArithSort] =
    ctx.mkAdd(numExps: _*)

  def mult(numExps: ArithExpr[_ <: ArithSort]*): ArithExpr[_ <: ArithSort] =
    ctx.mkMul(numExps: _*)

  def or(boolExps: BoolExpr*): BoolExpr =
    ctx.mkOr(boolExps: _*)

  def and(boolExps: BoolExpr*): BoolExpr =
    ctx.mkAnd(boolExps: _*)

  def or(col: Iterable[BoolExpr]): BoolExpr =
    or(col.toSeq: _*)

  def and(col: Iterable[BoolExpr]): BoolExpr =
    and(col.toSeq: _*)

  def ^(boolExp: BoolWrapper): BoolExpr = ctx.mkNot(boolExp)

  lazy val unInterpertedType: UninterpretedSort = ctx.mkUninterpretedSort(ctx.mkSymbol("U"));
  lazy val intType: IntSort = ctx.mkIntSort()
  lazy val realType: RealSort = ctx.mkRealSort()
  lazy val boolType: BoolSort = ctx.mkBoolSort()

  def getSort[T <: Expr[_ <: Sort]](m: Manifest[T]): Sort = {
    val clazz = m.runtimeClass.asInstanceOf[Class[T]]
    if (clazz == classOf[IntExpr])
      intType
    else if (clazz == classOf[RealExpr])
      realType
    else if (clazz == classOf[BoolExpr])
      boolType
    else throw new Exception("unsupported type")

  }

  case class Func[DOMAIN <: Expr[_ <: Sort], CODOMAIN <: Expr[_ <: Sort]](name: String)(implicit d: Manifest[DOMAIN], c: Manifest[CODOMAIN]) {
    val domain: Sort = getSort(d)
    val coDomain: Sort = getSort(c)
    val f: FuncDecl[_ <: Sort] = ctx.mkFuncDecl(name, domain, coDomain)

    def apply(e: Expr[_ <: Sort]*): CODOMAIN = {
      f.apply(e: _*).asInstanceOf[CODOMAIN]
    }
  }

  case class Z3Array[T <: Expr[_ <: Sort]](name: String)(size: Int)(implicit m: Manifest[T]) extends IndexedSeq[T] {

    val f: FuncDecl[_ <: Sort] = ctx.mkFuncDecl(name, intType, getSort(m))

    def apply(index: IntExpr): T = {
      f.apply(index).asInstanceOf[T]
    }

    def apply(index: Int): T = apply(IntWrapper(index))

    def length: Int = size

    def contains(e: T): BoolExpr =
      or(for (a <- this) yield a ~= e)

  }

  type ExprArray[E <: Expr[_ <: Sort]] = Array[E]

  trait ExprCompareable[E <: Expr[_ <: Sort]] {
    def <(e: E): BoolExpr

    def ~=(e: E): BoolExpr

    def <=(e: E): BoolExpr

    def >(e: E): BoolExpr

    def >=(e: E): BoolExpr
  }

  def ifelse(cond: BoolExpr, t: BoolExpr, f: BoolExpr): BoolExpr =
    (cond -> t) & (^(cond) -> f)

  case class Z3List[T <: Expr[_ <: Sort]](name: String)(implicit m: Manifest[T]) extends IndexedSeq[T] {
    private var s = 0

    private val f = ctx.mkFuncDecl(name, intType, getSort(m))

    def length: Int = s

    def apply(index: IntExpr): T = {
      f.apply(index).asInstanceOf[T]
    }

    def apply(index: Int): T = apply(IntWrapper(index))

    def +=(t: T): BoolExpr = {
      s += 1
      f.apply(s - 1) ~= t
    }

    /**
     * initiate first n elements
     */
    def init(n: Int) = {
      s = n
    }

    def containsExpr(t: T): BoolExpr =
      or(for (elem <- this) yield t ~= elem)

  }

}
