import stainless.lang._
import stainless.collection._

object QuickSort {

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
    case _ => true
  }

  def quickSort(list: List[BigInt]): List[BigInt] = {
    decreases(list.size, BigInt(0))
    list match {
      case Nil() => Nil[BigInt]()
      case Cons(x, xs) => par(x, Nil(), Nil(), xs)
    }
  } ensuring { res => isSorted(res)  && res.content == list.content }

  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    require(
      forall((y: BigInt) => l.contains(y) ==> y <= x) &&
      forall((y: BigInt) => r.contains(y) ==> y > x)
    )
    decreases(l.size+r.size+ls.size, ls.size)
    ls match {
      case Nil() => append(quickSort(l), consSorted(x, quickSort(r)))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  } ensuring {
    res => isSorted(res) && res.content == Set(x) ++ l.content ++ r.content ++ ls.content
  }

//Constructing a new list from a sorted list and an item that is smaller or equals than any element in the list results in a sorted list
  def consSorted(x: BigInt, ls: List[BigInt]): List[BigInt] = {
    require(isSorted(ls) && (ls.isEmpty || x <= ls.head))
    Cons(x, ls)
  } ensuring {
    res => isSorted(res) && res.content == Set(x) ++ ls.content
  }

  //Appending two sorted lists results in a sorted list if each element in the first list is smaller than each item in the second
  def append(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2) && (l1.isEmpty || l2.isEmpty || l1.last <= l2.head))
    l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }
  } ensuring {
    res => isSorted(res) && res.content == l1.content ++ l2.content
  }
}
