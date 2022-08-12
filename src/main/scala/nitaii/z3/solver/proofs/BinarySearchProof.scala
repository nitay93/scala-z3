package nitaii.z3.solver.proofs

import nitaii.z3.solver.Z3Utils._
import com.microsoft.z3.IntExpr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Status

object BinarySearchProof {

  /**
   * A proof of the correctness of binary search algorithm using SMT given a fixed array size
   * @param arraySize the size of the array
   */
  def proveForArrayOfSize(arraySize: Int) = {
    val s = newSolver
    val arr = Z3Array[IntExpr]("Array")(arraySize)
    val element = Z("element")
    val notInArray = Z("not in array")
    // find an assignment for:
    s.add(sorted(arr)) // a sorted array
    s.add(inArray(arr, element)) // that contains some element
    s.add(^(inArray(arr, notInArray))) // and does not contain another
    
    //can it be that it finds the one it shouldn't or doesn't find the one it should?
    s.add(^(binarySearchFinds(arr, element)) | binarySearchFinds(arr, notInArray)) 
    
    
    if ( s.check() == Status.SATISFIABLE ) {
      println("could not prove validity of binary search")
      println("found the following counter example:")
      println(s.getModel)
    }
    
    else {
      println(s"proved the correctness of the Binary Search Algorithm for arrays of size $arraySize")
    }
  }

  def sorted(arr: Z3Array[IntExpr]): BoolExpr =
    and((0 until arr.size - 1).map(i => arr(i) <= arr(i + 1)))

  def inArray(arr: Z3Array[IntExpr], element: IntExpr) =
    or(arr.map(e => e ~= element))

  /**
   * precondition: a sorted array, with element e, between start and end indexes
   * returns constraints that asserts:
   * the binary search method will find the element
   */

  def binarySearchFinds(arr: Z3Array[IntExpr], element: IntExpr, start: Int, end: Int): BoolExpr = {
    val size = end - start + 1
    val middle = (start + end) / 2

    if (start < end)
      ((arr(middle) > element) -> (binarySearchFinds(arr, element, start, middle - 1))) &
        ((arr(middle) < element) -> (binarySearchFinds(arr, element, middle + 1, end)))
    else if (start == end)
      arr(start) ~= element
    else false
  }

  def binarySearchFinds(arr: Z3Array[IntExpr], element: IntExpr): BoolExpr =
    binarySearchFinds(arr, element, 0, arr.size - 1)

    
  def binarySearch(arr: Array[Int], element: Int, start: Int, end: Int): Boolean = {
    val size = end - start + 1
    val middle = (start + end) / 2

    if (start < end) {
      if (arr(middle) > element)
        binarySearch(arr, element, start, middle - 1)
      else if (arr(middle) < element)
        binarySearch(arr, element, middle + 1, end)
      else true
    } else if (start == end)
      arr(start) == element
    else false
  }

}

//
//  def insert(arr: Func[IntExpr], index: Int, element: Z, arraySize: Int) = {
//    val updatedArr = Func[IntExpr]("UpdatedArray")(intType, intType)
//
//    (updatedArr,
//      (0 until index).map(i => arr(i) ~= updatedArr(i)).reduce(_ & _) &
//      (index + 1 until arraySize + 1).map(i => arr(i - 1) ~= updatedArr(i)).reduce(_ & _) &
//      (updatedArr(index) ~= element))
//  }