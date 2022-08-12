package nitaii.z3.solver.examples

import nitaii.z3.solver.proofs.UnionFindProof

object ProveUnionFind extends App {

  val makeSet = UnionFindProof.MakeSetProof(5)
  val find = UnionFindProof.FindProof(5)
  val unionDiff = UnionFindProof.UnionOfDiffSetsProof(5)
  val unionSame = UnionFindProof.UnionOfSameSetsProof(5)
  
  println("proving correctness for union find:")
    
  makeSet.prove
  find.prove
  unionDiff.prove
  unionSame.prove
  
  println("make set")
  makeSet.getExample
  println("union of elements in different sets")
  unionDiff.getExample
  println("union of elements in same set")
  unionSame.getExample
  
  
}

