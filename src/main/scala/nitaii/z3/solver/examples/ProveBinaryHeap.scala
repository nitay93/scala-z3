package nitaii.z3.solver.examples

import nitaii.z3.solver.proofs.MinBinaryHeapProof

object ProveBinaryHeap extends App {

  val findMin = MinBinaryHeapProof.FindMin(5)
  findMin.prove
  findMin.getExample

  val extractMin = MinBinaryHeapProof.ExtractMin(5)
  extractMin.prove
  extractMin.getExample
  
  val insert = MinBinaryHeapProof.SingleInsert(5)
  insert.prove
  insert.getExample

}