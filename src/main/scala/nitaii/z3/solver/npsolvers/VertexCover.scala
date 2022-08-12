package nitaii.z3.solver.npsolvers

case class VertexCover(vcount: Int, edges: Array[Array[Int]], costs: Array[Double]) {

  val vertices = 1 to vcount

  private def isValidInput =
    (for (edge <- edges) yield {
      edge.length == 2 && edge(0) <= vcount && edge(1) <= vcount && edge(0) != edge(1)
    }).reduce(_ && _) &&
      costs.length == vcount

  if (!isValidInput)
    throw new Exception("Vertex Cover : invalid input")

  private val matrix = edges.map(a => (a(0), a(1))).
    map { case (v, u) => getRowFor(u, v).map { x => x.toDouble} }

  private val b = (1 to edges.length).map(_ => -1.0).toArray

  private val solver = ZeroOneILP(matrix, b, costs, form = true)
  private val cover = solver.getSolution
  private val totalCost = solver.getGoalFunctionMinimalValue

  def getCover: Array[Int] = cover
  def getTotalCost: Double = totalCost

  def getRowFor(v: Int, u: Int): Array[Int] =
    vertices.map { vertex => if (vertex == v || vertex == u) -1 else 0 }.toArray[Int]

}