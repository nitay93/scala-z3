package nitaii.z3.solver.examples

import nitaii.z3.solver.npsolvers.ThreeDimMatching

object ThreeDimMatchingExample extends App {

  val T = Array(
    Array(1, 2, 3),
    Array(1, 2, 4),
    Array(2, 3, 5),
    Array(2, 4, 1),
    Array(4, 2, 3),
    Array(4,4,4))

  val prob = ThreeDimMatching(5, 5, 5, T, 3)
  if (prob.getM.isEmpty)
    println("could not find matching")
  else println("found the following matching : " + prob.getM.get)
}