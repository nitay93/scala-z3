package nitaii.z3.solver.proofs

import nitaii.z3.solver.Z3Utils._
import com.microsoft.z3.IntExpr
import com.microsoft.z3.BoolExpr

/**
 * A proof of MinBinaryHeap algorithms using SMT
 */
object MinBinaryHeapProof {

  // Proofs

  case class FindMin(heapSize: Int) extends Proof {

    val heap = new MinBinaryHeap
    val validity = heap.setValidityOf(heapSize)
    val min = Z("min")
    val setMin = (min ~= heap.findMin)

    def getSolver = {
      val solver = newSolver
      solver.add(validity) // let the heap be a valid heap
      solver add setMin
      solver
    }

    def getValidation = isMin(heap.arr, min)

    def proofMessage = s"proved find min operation for every heap of size $heapSize returns the minimum value in the heap and keeps it unchanged"

    def unableToProveMessage = "could not prove validity of find min operation"

    def unableToGetExample = s"could not find a valid example for a heap of size $heapSize of which findMin is valid"
  }

  case class ExtractMin(heapSize: Int) extends Proof {
    val heap = new MinBinaryHeap
    // let the heap be a valid heap
    val validity = heap.setValidityOf(heapSize)
    val (old, extracted, constraints) = heap.extractMin
    val validExtraction = wasExtracted(old, heap.arr, extracted)

    def getSolver = {
      val solver = newSolver

      solver add validity

      solver.add(constraints)

      solver
    }

    def getValidation = true
    (validExtraction & heap.isValid)

    def proofMessage = s"proved for every heap of size $heapSize extractMin operation is valid"

    def unableToProveMessage = "could not prove validation of extract min operation"

    def unableToGetExample = "could not find a valid example to extract min operation"
  }

  case class SingleInsert(heapSize: Int) extends Proof {

    val heap = new MinBinaryHeap
    val validity = heap.setValidityOf(heapSize)
    val elem = Z("new_element")
    val (old, insertion) = heap.insert(elem)

    def getSolver = {
      val solver = newSolver

      solver.add(validity) // let the heap be a valid heap
      solver.add(insertion) // insert element

      solver
    }

    def getValidation = heap.isValid & (heap contains elem) & and(for(e <- old) yield heap contains e)

    def proofMessage = s"proved that every insert to any heap of size $heapSize results in a valid heap"

    def unableToProveMessage = "could not prove validity of insertion"

    def unableToGetExample = s"could not find a valid example for an insert to a heap of size $heapSize"
  }

  // Minimum Binary Heap Implementation of Expression

  class MinBinaryHeap {
    var version = 0;
    var s = 0;

    def v = {
      version += 1
      version
    }

    def newArr(newSize: Int, symbol: String = "heap") =
      Z3Array[IntExpr](symbol + "_" + v)(newSize)

    var arr = newArr(size)

    def size = s

    def insert(e: IntExpr) = {
      val old = newArr(size, "old_copy")
      val oldHeapConstraints = copyElements(arr, old, 0 until size)

      val updated = newArr(size + 1)
      val heapifyConstraints = heapifyUp(updated, e, size)

      arr = updated
      s += 1

      (old, heapifyConstraints & oldHeapConstraints)
    }

    //    private def heapifyUp(updated: VarArray[IntExpr], e: IntExpr, i: Int): BoolExpr = {
    //      val parent = getParent(i)
    //      if (!parent.isEmpty)
    //        (arr(parent.get) <= e) -> ((updated(i) ~= e) & // if the parent <= e than i is the right index for e
    //          copyElements(arr, updated, (0 until i))) & // and we copy the rest of the updated array will be the same as before
    //          (arr(parent.get) > e) -> (heapifyUp(updated, e, parent.get) & // otherwise, we need to heapify up again
    //            (updated(i) ~= arr(parent.get)) & // the parent will be set to be in the ith index
    //            copyElements(arr, updated, (parent.get + 1 until i))) // we can copy the rest of the elements between i and the parent index
    //      else (updated(0) ~= e)
    //    }

    private def heapifyUp(updated: Z3Array[IntExpr], e: IntExpr, i: Int): BoolExpr = {
      val parent = getParent(i)
      if (!parent.isEmpty)
        ifelse(
          arr(parent.get) <= e,
          (updated(i) ~= e) & // if the parent <= e than i is the right index for e
            copyElements(arr, updated, (0 until i)), // and we copy the rest of the updated array will be the same as before
          heapifyUp(updated, e, parent.get) & // otherwise, we need to heapify up again
            (updated(i) ~= arr(parent.get)) & // the parent will be set to be in the ith index
            copyElements(arr, updated, (parent.get + 1 until i))) // we can copy the rest of the elements between i and the parent index
      else (updated(0) ~= e)
    }

    def findMin: IntExpr = arr(0)

    def extractMin = {
      if (isEmpty)
        throw new Exception("heap is already empty")

      val extracted = findMin
      val updated = newArr(size - 1, "extracted_heap")
      val heapityDownConstraints = heapifyDown(updated, 0, arr(size - 1))
      val old = newArr(size, "old_copy")
      val oldHeapConstraints = copyElements(arr, old, 0 until size)

      arr = updated
      s -= 1

      (old, extracted, heapityDownConstraints & oldHeapConstraints)
    }

    def heapifyDown(updated: Z3Array[IntExpr], i: Int, e: IntExpr): BoolExpr = {
      val left = if (2 * i + 1 < updated.size)
        Some(arr(2 * i + 1))
      else None;

      val right =
        if (2 * i + 2 < updated.size)
          Some(arr(2 * i + 2))
        else None

      if (!left.isEmpty)
        if (!right.isEmpty)

          ifelse(left.get < e | right.get < e, // if e is grater than one of its children
            ifelse(left.get <= right.get, // if left is less than right 
              // heapify down left
              (updated(i) ~= left.get) & copyElements(arr, updated, (i + 1 until 2 * i + 1)) & heapifyDown(updated, 2 * i + 1, e),
              // else, heapify down right
              (updated(i) ~= right.get) & copyElements(arr, updated, (i + 1 until 2 * i + 2)) & heapifyDown(updated, 2 * i + 2, e)),
            // else (if e is not grater than the children) set e to be at this index
            (updated(i) ~= e) & (copyElements(arr, updated, (i + 1 until updated.size))))

        //        else (updated(i) ~= left.get) & copyElements(arr, updated, (i + 1 until updated.size))
        // i has only left child
        else ifelse(e > left.get, // if e is grater than i's child
          (updated(i) ~= left.get) & (updated(2 * i + 1) ~= e), // left child is set to index i with one (left) child of value e
          (updated(i) ~= e) & (updated(2 * i + 1) ~= left.get)) & // e is set to the i's position and left child stays still
          copyElements(arr, updated, (i + 1 until 2 * i + 1)) // in any case copy the elements into the updated heap array
      else (updated(i) ~= e) & copyElements(arr, updated, (i + 1 until updated.size)) // if i has no children it's safe to put e in this spot
    }

    def isEmpty = size == 0

    def isValid = {
      and(
        (0 until size).map(i => {

          val validFirstChild: BoolExpr =
            if (2 * i + 1 < size)
              arr(i) <= arr(2 * i + 1)
            else true

          val validSecondChild: BoolExpr =
            if (2 * i + 2 < size)
              arr(i) <= arr(2 * i + 2)
            else true

          validFirstChild & validSecondChild

        }))

    }

    def setValidityOf(s: Int) = {
      this.s = s
      arr = newArr(size)
      isValid
    }

    // Heap Helper Methods

    private def copyElements(a1: Z3Array[IntExpr], a2: Z3Array[IntExpr], indexes: Seq[Int]) =
      and((for (i <- indexes) yield a1(i) ~= a2(i)): _*)

    private def getParent(i: Int) =
      if (i == 0)
        None
      else if (i % 2 == 0)
        Some(i / 2 - 1)
      else Some(i / 2)

    def contains(elem: IntExpr) = {
      arr contains elem
    }
  }

  // Helper Methods

  def isMin(arr: Z3Array[IntExpr], min: IntExpr) = {
    val lessThanAnyConstraints = for (e <- arr) yield min <= e
    and(and(lessThanAnyConstraints) & arr.contains(min))
  }

  def wasExtracted(old: Z3Array[IntExpr], updated: Z3Array[IntExpr], extracted: IntExpr) =
    and(for (e <- old) yield (updated.contains(e) | (e ~= extracted))) & // every element in old is either in updated or the extracted one
      (old.size ~= updated.size + 1) &
      isMin(old, extracted)

}