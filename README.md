# scala-z3
Scala API for Z3 SAT solver

This tool extends the Z3 Java API to Scala.
Enabling easy, readable and fun API for a SAT Solver.

### Build the project:
1. Download the native Z3 distribution for your machine from https://github.com/Z3Prover/z3/releases. (Tested on version 4.9.1) 
2. Unzip and extract the com.microsoft.z3.jar file.
3. Install the jar file to your local maven repository:
````
mvn install:install-file \
   -Dfile=com.microsoft.z3.jar \
   -DgroupId=com.microsoft \
   -DartifactId=z3 \
   -Dversion=4.9.1 \
   -Dpackaging=jar \
   -DgeneratePom=true
````
4. In case you downloaded a different version. Update the z3 artifact version in the build.sbt file
5. Finally, build the z3-scala jar with `sbt clean compile package`

### The API

The z3 Scala API can be found in `nitaii.z3.solver.Z3Utils` object.
Simply import the content of object to use the API.

Example: 
```scala
import nitaii.z3.solver.Z3Utils._

object Test extends App {
  
  // define an expression: x1 and not(x2) = x3
  // where x1, x2, x3 are boolean variables 
  val expression = B("x1") & ^(B("x2")) ~= B("x3")
  
  // initiate the SAT solver
  val solver = newSolver
  solver.add(expression)
  
  // is the expression satisfiable
  assert(solver.check() == 
    com.microsoft.z3.Status.SATISFIABLE)
  
  // get the SAT model
  solver.getModel
}
```

Check out the next sections of NP Solvers and Proofs to find out more complex examples of using z3 Scala API. 

### NP Solvers
The `npsolver` package contains a series of NP-complete problems that can be reduced to SAT.
The package reduces the given problem into a SAT expression and provides the solution.
Examples for using the NP Solvers can be found in the `examples` package.

### Proofs
SAT solvers can also be utilized to prove algorithms.
In the `proofs` package you can find a reduction of some 
common algorithms into an expression that asserts the result of the algorithm equals the desired value.
Using z3 we can assert that the expression is satisfiable and thus the algorithm is valid.
