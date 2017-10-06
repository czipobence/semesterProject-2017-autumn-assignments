import stainless.lang._
import stainless.collection._

object Slicing {

  //Is there any way to tell stainless that (l1 ++ l2).size == l1.size + l2.size
  def appendSize[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 ++ l2).size == l1.size + l2.size
  }.holds

  // (l1 ++ l2).take(l1.size) == l1
  def appendTakeFirst[T](l1: List[T], l2: List[T]): Boolean = {
    ListSpecs.appendTakeDrop(l1, l2, l1.size)
  }.holds

  // (l1 ++ l2).drop(l1.size) == l2
  def appendTakeLast[T](l1: List[T], l2: List[T]): Boolean = {
    ListSpecs.appendTakeDrop(l1, l2, l1.size)
  }.holds

}
