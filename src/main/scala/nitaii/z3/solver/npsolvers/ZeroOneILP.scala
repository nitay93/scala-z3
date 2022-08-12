package nitaii.z3.solver.npsolvers

import nitaii.z3.solver.Z3Utils._
import com.microsoft.z3.Status

/**
 * solving the 0-1 linear programming problem which is NPC
 * the problem is reprressented in the canonical/standard form (true for canonical, false for standard)
 * for constraints Ax <= b
 * we want to minimize the goal function cx
 * where c,b are vectors A is a matrix.
 * the solution is x is a vector of 0 and 1
 */

case class ZeroOneILP(matrix: Array[Array[Double]], b: Array[Double], c: Array[Double], form: Boolean, from: Int = -999999, to: Int = 999999, accuracy: Double = 0.01) {

  if (matrix.isEmpty)
    throw new Exception("empty problem is not allowed")

  if (matrix.length != b.length)
    throw new Exception("matrix rows and b vector are not of have the same dimension")

  if (matrix(0).length != c.length)
    throw new Exception("matrix columns and c vector are not of the same dimension")

  if (from >= to)
    throw new Exception("range (from,to) has to be a valid range")

  val varCount = c.length

  /**
   * solving the decision problem.
   * Is there a solution in which the goal function is smaller than t
   */
  private def solveDecisionOn(t: Double): Option[Array[Int]] = {
    val s = newSolver
    val x = (1 to varCount).map(i => Z(s"x$i")).toArray
    for (xi <- x) {
      s add ((xi ~= 0) | (xi ~= 1))
    }

    for ((row, i) <- matrix.zipWithIndex) {
      val rowSum = getSum(row, x)
      if (form)
        s add (rowSum <= b(i))
      else s add (rowSum ~= b(i))
    }

    val goalFunction = getSum(c, x)
    s add (goalFunction <= t)

    val status = s.check()
    if (status == Status.SATISFIABLE) {
      val model = s.getModel
      Some(
        for (xi <- x) yield {
          val v = model.evaluate(xi, false)
          if (v == ctx.mkInt(1))
            1
          else if (v == ctx.mkInt(0))
            0
          else throw new Exception("Something went wrong")
        })
    } else None
  }

  private def getSum(coef: Array[Double], variables: Array[Z]) = {
    val summends = for ((entry, j) <- coef.zipWithIndex) yield {
      variables(j) * entry
    }
    summends.reduce(_ + _) //.reduce((s1,s2) => s1+s2)
  }

  if (!solveDecisionOn(from).isEmpty)
    throw new Exception(s"Problem might not be bounded (or solution is not in the range ($from, $to))")

  val biggestSolution = solveDecisionOn(to)
  if (solveDecisionOn(to).isEmpty)
    throw new Exception(s"Problem might not have a solution (or the solution is not in the range ($from, $to)")

  var currentSolution: Option[Array[Int]] = None
  var (start, end) = (from.toDouble, to.toDouble)

  while (end - start > accuracy) {
    val mid = (end + start) / 2.0
    val sol = solveDecisionOn(mid)
    if (sol.isEmpty) // is there no solution for mid
    // any solution must be larger than mid
      start = mid
    else { // mid is a solution, but still might not be optimal
      end = mid
      currentSolution = sol
    }
  }

  if (currentSolution.isEmpty)
    currentSolution = solveDecisionOn(to)

  // the smallest solution that was found
  private val solutionValue = currentSolution.get.zip(c).map {
    case (x, c) => c * x
  }.sum

  def getSolution = currentSolution.get

  def getGoalFunctionMinimalValue = solutionValue

  //  private def getDecimalCount(d : Double) = {
  //    val text = (Math.abs(d)).toString();
  //    val integerPlaces = text.indexOf('.');
  //    text.length - integerPlaces - 1;
  //  }
  //
  //  private def round(d : Double) = {
  //    val dc = c.map { ci => getDecimalCount(ci) }.max
  //    BigDecimal(d).setScale(dc, BigDecimal.RoundingMode.HALF_UP).toDouble
  //  }

}

/**
 * for java compatibility
 */
object ZeroOneILP {
  def of(matrix: Array[Array[Double]], b: Array[Double], c: Array[Double], form: Boolean) =
    ZeroOneILP(matrix, b, c, form)
}