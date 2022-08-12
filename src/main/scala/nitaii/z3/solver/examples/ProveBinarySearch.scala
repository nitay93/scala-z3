package nitaii.z3.solver.examples

import nitaii.z3.solver.proofs.BinarySearchProof

object ProveBinarySearch extends App {
  
  BinarySearchProof.proveForArrayOfSize(6)
}