package nitaii.z3.solver.proofs

import nitaii.z3.solver.Z3Utils._
import com.microsoft.z3.{BoolExpr, Expr, IntExpr, Sort}

object UnionFindProof {

  case class FindProof(size: Int) extends Proof {
    
    private val uf = new UnionFind[IntExpr]
    private val validity = uf.setValidityOf(size)
    

    def getSolver = {
      val solver = newSolver
      solver add validity 
      solver
    }
    
    def getValidation: BoolExpr = uf.findOperationValidation
    def proofMessage: String = s"proved validity of find operation to any union find of size $size"
    def unableToProveMessage: String = "validation faild. could not prove validity of find operation"
    def unableToGetExample: String = s"could not find an example of a valid union find of size $size in which find operation is successful"
  }

  case class UnionOfDiffSetsProof(size: Int) extends Proof {
    

    private val uf = new UnionFind[IntExpr]
    val validity = uf.setValidityOf(size)
    private val (e1, e2, notInTheSameSet) = uf.notInTheSameSet
    private val union = uf.union(e1, e2)
    
    def getSolver = {
      val solver = newSolver
      solver add validity
      solver add notInTheSameSet
      solver add union
      solver
    }
    
    def getValidation: BoolExpr = uf.isValid
    def proofMessage: String = s"proved validity of find operation to any union find of size $size"
    def unableToProveMessage: String = "validation faild. could not prove validity of find operation"
    def unableToGetExample: String = s"could not find an example of a valid union find of size $size in which find operation is successful"
  }
  
  case class UnionOfSameSetsProof(size: Int) extends Proof {
    
    private val uf = new UnionFind[IntExpr]
    private val validity = uf.setValidityOf(size)
    
    private val (e1, e2, notInTheSameSet) = uf.notInTheSameSet
    val union = uf.union(e1, e2) 
    
    def getSolver = {
      val solver = newSolver
      solver add validity
      solver add ^(notInTheSameSet) //e1 and e2 are in the same set
      solver add union  
      solver
    }
    
    
    def getValidation: BoolExpr = uf.isValid // & uf2.isValid
    def proofMessage: String = s"proved validity of find operation to any union find of size $size"
    def unableToProveMessage: String = "validation faild. could not prove validity of find operation"
    def unableToGetExample: String = s"could not find an example of a valid union find of size $size in which find operation is successful"
  }

  
   case class MakeSetProof(size: Int) extends Proof {
    

    private val uf = new UnionFind[IntExpr]
    private val validity = uf.setValidityOf(size)
    private val element = Z("new_element")
    private val makeSet = uf.makeSet(element)
        
    def getSolver = {
      val solver = newSolver
      solver add validity
      solver add makeSet
      solver
    }
    
    def getValidation: BoolExpr = uf.isValid & uf.isolated(element)
    def proofMessage: String = s"proved validity of find operation to any union find of size $size"
    def unableToProveMessage: String = "validation faild. could not prove validity of find operation"
    def unableToGetExample: String = s"could not find an example of a valid union find of size $size in which make set operation is successful"
  }


  def log2(x: Int): Double = Math.log(x) / Math.log(2)
  
  

  class UnionFind[T <: Expr[_ <: Sort]](implicit m: Manifest[T]) {
    def size = all.length
    lazy val count = UnionFind.getCount
    private[UnionFindProof] val all = Z3List[T]("all id"+count)
    private[UnionFindProof] var (getParent, getRep, getDeg) = newStructures
    private def maxDeg = log2(size).floor.toInt
    
    private val old : Option[UnionFind[T]] = None

    var version = 0
    private def newStructures = {
      version += 1
      (Func[T,T](s"parents id$count v$version"), // parents map
        Func[T, T](s"reps id$count v$version"), // reps map
        Func[T, IntExpr](s"degrees id$count v$version")) // degree map
    }

    //  *** Validity  **** 

    def isValid: BoolExpr = {

      val degreeConstraints = for (elem <- all) yield {
        ifelse(childless(elem),
          (getDeg(elem) ~= 0),
          //otherwise the degree is larger than any of its children and is larger than at least one of them in by exactly 1
          and(all.filter(e => e != elem).map {
            e => ((getParent(e) ~= elem) -> (getDeg(elem) >= (getDeg(e) + 1)))
          }) &
            or(all.filter(e => e != elem).map {
              e => (getParent(e) ~= elem) & (getDeg(elem) ~= (getDeg(e) + 1))
            }))

      }

      //every element with degree d has a child with every degree between 0 to d-1
      val flatTree =
        for (elem <- all) yield {
          and(
            for (d <- 0 to maxDeg) yield {
              (getDeg(elem) > d) -> hasChildWithDeg(elem, d)
            })
        }

      val allElementsAreDifferent =
        //        all.zip(all).filter{case(e1,e2)=> e1 != e2 }.map{case(e1,e2) => ^(e1 ~= e2)})
        all.combinations(2).map { e => ^(e(0) ~= e(1)) }

      // parents and reps are elements in the union find
      val validityOfMaps =
        (for (elem <- all) yield {
          (all containsExpr getParent(elem)) &
            (all containsExpr getRep(elem))
        })

      val treeConstraints =
        for (elem <- all) yield {
          (isRep(elem) <-> (getParent(elem) ~= elem)) & // elem is a rep if it is his own parent
            (getRep(elem) ~= getRep(getParent(elem)))
        }

      //elements that are only child cannot have children, and it has to have a childless uncle
      //      val flatTree = for (elem <- all) yield (onlyChild(elem) -> 
      //      (childless(elem) &
      //      (^(isRep(getParent(elem))) -> hasChildlessUncle(elem))))      

      val allReachesReps = for (elem <- all) yield reachesRep(elem)

      and(allElementsAreDifferent.toSeq) &
        and(flatTree) &
        and(validityOfMaps) &
        and(treeConstraints) &
        and(allReachesReps) &
        and(degreeConstraints)
    }

    def setValidityOf(size: Int): BoolExpr = {
      all.init(size)
      isValid
    }

    def findOperationValidation = {
      and(
        for (elem <- all) yield (getRep(elem) ~= find(elem)))
    }

    // ***** Helper predicates and methods ****

    private def reachesRep(elem: T) = {
      getRep(elem) ~= getAncestor(elem, maxDeg)
    }

    private def getAncestor(elem: T, d: Int): T = {
      if (d == 0)
        elem
      else getAncestor(getParent(elem), d - 1)
    }

    private def isRep(elem: T): BoolExpr = elem ~= getRep(elem)

    private def onlyChild(elem: T): BoolExpr = and(
      all.filter { e => e != elem }.map { e => ^(getParent(e) ~= getParent(elem)) }) & ^(isRep(elem))

    private def childless(elem: T): BoolExpr = { // the only child it can have is itself
      and(all.map { e => ((getParent(e) ~= elem) -> (e ~= elem)) })
    }

    //    private def hasChildlessUncle(elem : T) : BoolExpr = or(
    //      for (e <- all) yield (
    //          (getParent(e) ~= getParent(getParent(elem))) &
    //          childless(e)
    //      ))
    private def hasChildWithDeg(elem: T, d: IntExpr) =
      or(for (e <- all) yield {
        (getParent(e) ~= elem) & (getDeg(e) ~= d)
      })


    // ***** Union Find operations *****

    def makeSet(element: T) = {
      (getDeg(element) ~= 0) &
        and(for (elem <- all) yield ^(element ~= elem)) & // element is new (no other element with this value)
        (all += element) & // adding the element to the list of element
        (getParent(element) ~= element) & (getRep(element) ~= element) // element is in its own set
    }

    def find(element: T) = {
      getAncestor(element, maxDeg)
    }
    

    def union(e1: T, e2: T) = {
      val rep1 = find(e1)
      val rep2 = find(e2)
      val sameReps = (rep1 ~= rep2)

      ifelse(getDeg(rep1) > getDeg(rep2),
        join(rep1, rep2),
        join(rep2, rep1))
        
    }

    /**
     * requires rep1 and rep2 are actually reps.
     * rep2 is going to be under rep1
     */
    private def join(rep1: T, rep2: T): BoolExpr = {
      val (newGetParent, newGetRep, newGetDeg) = newStructures
 
      updateParentJoin(rep1, rep2, newGetParent) &
        updateRepJoin(rep1, rep2, newGetRep) &
        updateDegJoin(rep1, rep2, newGetDeg)
    }

    private def updateParentJoin(parent: T, e: T, newGetParent: Func[T,T]): BoolExpr = {
      val constrait = (parent ~= newGetParent(e)) &
        and(
          for (elem <- all) yield {
            ^(newGetParent(elem) ~= getParent(elem)) -> (elem ~= e)
          })

      getParent = newGetParent

      constrait
    }

    private def updateRepJoin(newRep: T, oldRep: T, newGetRep: Func[T,T]): BoolExpr = {
      val constraint = and(
        for (elem <- all) yield {
          ifelse(getRep(elem) ~= oldRep,
            newGetRep(elem) ~= newRep,
            newGetRep(elem) ~= getRep(elem))
        })

      getRep = newGetRep

      constraint
    }

    private def updateDegJoin(parent: T, e: T, newGetDeg: Func[T, IntExpr]): BoolExpr = {
      val sameExceptParent = and(
        for (elem <- all) yield (^(getDeg(elem) ~= newGetDeg(elem)) -> (elem ~= parent)))

      val sameDegrees = and(
        for (elem <- all) yield (getDeg(elem) ~= newGetDeg(elem)))

      val constraint = ifelse(
        getDeg(parent) ~= getDeg(e),
        (newGetDeg(parent) ~= getDeg(parent) + 1) & sameExceptParent,
        sameDegrees)

      getDeg = newGetDeg

      // if reps are equal, the data structure should not change and therefore also the degrees
      ifelse(e ~= parent, sameDegrees, constraint)
    }

    /**
     * requires has at least 2 elements
     */
    def notInTheSameSet = {
      val e1 = all(0)
      val e2 = all(1)

      (e1, e2, ^(getRep(e1) ~= getRep(e2)))
    }
    
    def isolated(element : T) : BoolExpr = {
      and(
      for(elem <- all) yield (getRep(element) ~= getRep(elem)) -> (element ~= elem))
    }
  }
  
  
  
  object UnionFind {
    var count = 0
    def getCount = {
      count += 1
      count
    }
  }
}