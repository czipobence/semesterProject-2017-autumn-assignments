import stainless.lang._
import stainless.lang.Set._
import stainless.collection._
import stainless.collection.ListSpecs._
import stainless.proof._

object Star {
  type Lang[T] = Set[List[T]]
  type ScalaSet[T] = scala.collection.immutable.Set[T]

  def setListToSetList[T](s: ScalaSet[List[T]], identity: Lang[T]): Lang[T] = {
    s.foldLeft(identity)((s, item) => s + item)
  }

  def concatAll[T](l1: Lang[T], l2: Lang[T]): Lang[T] = {
    val a = for (w1 <- l1.theSet; w2 <- l2.theSet)
      yield (w1 ++ w2)
    setListToSetList(a, Set())
  }

  //ensuring {res : Set[List[T]] => forall( (y1:List[T]) => l1.contains(y1) ==> (forall( (y2:List[T]) => l2.contains(y2) ==> res.contains(y1 ++ y2)  ))  )}

  /*def cancellationLaw[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    (l2 == l3) ==> (concatAll(l1, l2) == concatAll(l1,l3) )
  }.holds

  def heads[T](l: Lang[T]): scala.collection.immutable.Set[T] = {
    l.filter(x => !x.isEmpty).map(x => x.head)
  }

  def headsCons[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    heads(l1) == heads(concatAll(l1, l2))
  }.holds

  def predHead[T](head: T, l1: Lang[T]): Boolean = {
    require(! heads(l1).contains(T))
    forall((x: List[T]) => l1.contains(x) ==> l1.head != head )
  }.holds*/

}
