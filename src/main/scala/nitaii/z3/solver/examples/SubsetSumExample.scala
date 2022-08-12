package nitaii.z3.solver.examples

import nitaii.z3.solver.npsolvers.SubsetSum

object SubsetSumExample extends App {
  
  val subset = SubsetSum.solveFor(Set(2,5,1,3,7,9,3), 15)
  if(subset.isEmpty)
    println("could not find such subset")
  else println("subset found : " + subset.get)
  
}