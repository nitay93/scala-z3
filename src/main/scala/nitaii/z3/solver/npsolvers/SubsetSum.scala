package nitaii.z3.solver.npsolvers

import nitaii.z3.solver.Z3Utils._
import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, IntExpr, Status}
import nitaii.z3.solver.Z3Utils

import scala.jdk.CollectionConverters._

object SubsetSum {
  val boolToInt = Func[BoolExpr, IntExpr]("Bool2Int")
  val boolToIntConstraint = (boolToInt(true) ~= 1) & (boolToInt(false) ~= 0)

  def subsetSum(set: Set[Double], sum: Double): Set[Double] = subsetSum(set, sum)

  def solveFor(set: Set[Double], sum: Double): Option[Set[Double]] = {
    val isInSubSet = set.map { num => (num, B(s"is $num in subset")) }

    val summand = isInSubSet.map { case (num, bool) => boolToInt(bool) * num }
    val summation = Z3Utils.sum(summand.toSeq: _*)

    val s = newSolver
    s.add(boolToIntConstraint)
    s.add(summation ~= sum)
    if (Status.SATISFIABLE == s.check()) {
      val model = s.getModel
      val subset =
        isInSubSet
          .filter { case (_, variable) => model.evaluate(variable, false) == ctx.mkBool(true) }
          .map { case (num, _) => num }

      if (subset.isEmpty)
        None
      else Some(subset)
    } 
    else None
  }

  // Java support

  def javaSolveFor(set: java.util.Set[Double], sum: Double): java.util.Set[Double] = {
    val solution = solveFor(set.asScala.toSet, 1)
    if (solution.isEmpty)
      null
    else solution.get.asJava
  }

}