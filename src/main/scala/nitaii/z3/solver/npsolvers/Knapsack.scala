package nitaii.z3.solver.npsolvers

case class Knapsack(weights :Array[Double], values : Array[Double], capacity : Double) {
  
  lazy val solver = ZeroOneILP(Array(weights), Array(capacity), values.map(x => -x), true)
  
  def getSolution: Array[Int] = solver.getSolution
  def getValue: Double = -solver.getGoalFunctionMinimalValue
  
}