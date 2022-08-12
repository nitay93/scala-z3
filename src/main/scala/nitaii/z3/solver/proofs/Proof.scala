package nitaii.z3.solver.proofs

import com.microsoft.z3.Solver
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Status
import nitaii.z3.solver.Z3Utils._

object Proof {

  def proveCorrectness(s: Solver, validation: BoolExpr) = {
    s add ^(validation)
    val status = s.check()
    (status == Status.UNSATISFIABLE)
  }

  def getExample(s: Solver, validation: BoolExpr) = {
    s add validation
    val status = s.check()
    if (status == Status.SATISFIABLE)
      Some(s.getModel)
    else None
  }
}

trait Proof {
  def getSolver: Solver
  def getValidation: BoolExpr
  def proofMessage: String
  def unableToProveMessage: String
  def unableToGetExample: String

  def prove = {
    if (Proof.proveCorrectness(getSolver, getValidation))
      println(proofMessage)
    else {
      println(unableToProveMessage)
      println("counter example:")
      println(getSolver.getModel)
    }
  }

  def getExample = {
    val example = Proof.getExample(getSolver, getValidation)
    if (!example.isEmpty) {
      println("Example : ")
      println(example.get)
    } else {
      println(unableToGetExample)
    }
  }

}