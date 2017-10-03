import stainless.lang._
import stainless.collection._

object Language {

  def dropFromBoth[T](l1: List[T], l2: List[T], n: BigInt): (List[T], List[T]) = {
    (l1.drop(n), l2.drop(n))
  } ensuring {res => (l1 == l2) ==> (res._1 == res._2)}

  def cancelLeft[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    require((l1 ++ l2) == (l1 ++ l3))
    val (res1, res2) = dropFromBoth(l1 ++ l2, l1 ++ l3, l1.size)
    res1 == res2
  }.holds

  def takeFromBoth[T](l1:List[T], l2: List[T], n: BigInt): (List[T], List[T]) = {
    (l1.take(n), l2.take(n))
  } ensuring {res => (l1 == l2) ==> (res._1 == res._2)}

  def cancelRight[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    require((l2 ++ l1) == (l3 ++ l1))
    val (res1, res2) = takeFromBoth(l2 ++ l1, l3 ++ l1, l2.size)
    res1 == res2
  }.holds

}
