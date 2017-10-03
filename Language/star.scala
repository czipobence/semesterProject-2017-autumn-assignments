import stainless.lang._
import stainless.collection._
import stainless.collection.ListSpecs._
import stainless.proof._

object Star {
  type Lang[T] = scala.collection.immutable.Set[List[T]]

  def concatAll[T](l1: Lang[T], l2: Lang[T]): Lang[T] = {
    val a = for (w1 <- l1.toList; w2 <- l2.toList)
      yield (w1 ++ w2)
    a.toSet
  } ensuring {res : Lang[T] => forall( (y1:List[T]) => l1.contains(y1) ==> (forall( (y2:List[T]) => l2.contains(y2) ==> res.contains(y1 ++ y2)  ))  )}



}
