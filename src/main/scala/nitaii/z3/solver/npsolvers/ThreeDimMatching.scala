package nitaii.z3.solver.npsolvers

import nitaii.z3.solver.Z3Utils._
import com.microsoft.z3._

case class ThreeDimMatching(xSetSize: Int, ySetSize: Int, zSetSize: Int, T: Array[Array[Int]], matching: Int) {

  private val xSet = 1 to xSetSize
  private val ySet = 1 to ySetSize
  private val zSet = 1 to zSetSize

  private def isInputValid = {
    val everyEntryOfTOfSize3 =
      (for (arr <- T) yield {
        arr.length == 3
      }).reduce(_ && _)

    val validEntries =
      (for (arr <- T) yield {
        (xSet contains arr(0)) &&
          (ySet contains arr(1)) &&
          (zSet contains arr(2))
      }).reduce(_ && _)

    everyEntryOfTOfSize3 && validEntries
  }

  if (!isInputValid)
    throw new Exception("ThreeDimMatching : invalid input")

  private val solver = newSolver
  private val M = (1 to matching).map(i => (Z(s"a$i"), Z(s"b$i"), Z(s"c$i")))

  // M is subset of t
  private val subSetOfT =
    for((a,b,c) <- M) yield {
      inT(a,b,c)
    }

  private val differentEntries =
    M.combinations(2).map(seq => (seq(0), seq(1))).map {
      case ((a1, b1, c1), (a2, b2, c2)) => {
        ^(a1 ~= a2) & ^(b1 ~= b2) & ^(c1 ~= c2)
      }
    }
  
  def inT(a:IntExpr,b:IntExpr,c:IntExpr): BoolExpr = {
    or(T.map { arr => (arr(0), arr(1), arr(2)) }.map{
      case (x,y,z) => {
        (x ~= a) & (y ~= b) & (z ~= c)
      }
    })
  }

  solver add and(differentEntries.toSeq)
  solver add and(subSetOfT)

  def getSolver: Solver = solver
  def getJavaM: Array[Array[Expr[IntSort]]] = javaSolution
  def getM: Option[IndexedSeq[(Expr[_ <: Sort], Expr[_ <: Sort], Expr[_ <: Sort])]] = solution

  private val solution =
    if (solver.check() == Status.SATISFIABLE) {
      val model = solver.getModel
      Some(for ((a, b, c) <- M) yield {
        val aval = model.evaluate(a, false)
        val bval = model.evaluate(b, false)
        val cval = model.evaluate(c, false)
        (aval, bval, cval)
      })

    } else None

  private val javaSolution =
    if (solution.isEmpty)
      null
        else solution.get
          .map(t => Array(t._1,t._2,t._3)).toArray

}