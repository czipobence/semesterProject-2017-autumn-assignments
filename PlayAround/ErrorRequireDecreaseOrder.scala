import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

object Sample{

  //I think this is the same issue that I had with the function below.
  /**
  Verification result:
    [Warning ]  => INVALID
    [Warning ] Found counter-example:
    [Warning ]   x: T        -> T#8
    [Warning ]   l1: List[T] -> Cons[T](T#6, Nil[T]())
    [Warning ]   l2: List[T] -> Cons[T](T#7, Nil[T]())
  */
  def requireDecreaseWrongOrder[T](l1: List[T], l2: List[T], x: T): Boolean = {
    decreases(l1.size)
    require(l1.content == l2.content)
    (l1-x).content == (l2-x).content
  }.holds

  /*def contentTraversesAA[T](l1: List[List[T]], l2: List[List[T]], suffix: List[T]): Boolean = {
    require(l1.content == l2.content)
    decreases(l1.size)
    appendToAll(l1, suffix).content == appendToAll(l2,suffix).content because {
      l1 match {
        case Nil() => true
        case x :: xs if xs.contains(x) => {
          check {xs.content == (x::xs).content} &&
          check {appendToAll(x::xs, suffix).content == ( (x++suffix) ::appendToAll(xs,suffix)).content} &&
          check {( (x++suffix) ::appendToAll(xs,suffix)).content == appendToAll(xs,suffix).content because {appendToAllContains(xs,suffix,x)}}
          check {appendToAll(xs,suffix).content == appendToAll(l2,suffix).content because { (xs.content == l2.content) && contentTraversesAA(xs,l2,suffix)}}
        }
        case x :: xs  => {
          check {appendToAll(x::xs, suffix).content == ((x++suffix) :: appendToAll(xs,suffix)).content} &&
          check {((x++suffix) :: appendToAll(xs,suffix)).content == Set(x++suffix) ++ appendToAll(xs,suffix).content} &&
          check {Set(x++suffix) ++ appendToAll(xs,suffix).content ==  Set(x++suffix) ++ appendToAll(l2-x,suffix).content because {contentTraversesAA(xs, l2-x, suffix)}} &&
          check {Set(x++suffix) ++ appendToAll(l2-x,suffix).content == ((x++suffix) :: appendToAll(l2-x,suffix)).content} &&
          check {((x++suffix) :: appendToAll(l2-x,suffix)).content == appendToAll(l2,suffix).content because {appendToAllRemoveAndAdd(l2,suffix,x)}}
        }
      }
    }
  }.holds*/
}
