import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._


/* Useful and not-so-useful theorems about lists that are not in ListSpecs*/
object ListSpecsExt {

  /*
   * Snocing an item to the first list is equivalent consing to the second if we append the two lists
   */
  def snocGoesHead[T](l1: List[T], x: T,l2: List[T]) : Boolean = {
    ((l1 :+ x) ++ l2) == (l1 ++ (x :: l2)) because {
      ((l1 :+ x) ++ l2)                 ==| ListSpecs.snocIsAppend(l1,x)                      |
      ((l1 ++ Cons[T](x, Nil())) ++ l2) ==| ListSpecs.appendAssoc(l1, Cons[T](x, Nil()), l2)  |
      l1 ++ (Cons[T](x, Nil()) ++ l2)   ==| trivial                                           |
      l1 ++ (x :: l2)
    }.qed
  }.holds

  //true for one direction
  def reverseSameHelper1[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 == l2) ==> (l1.reverse == l2.reverse)
  }.holds

  //true for back
  def reverseSameHelper2[T](l1: List[T], l2: List[T]): Boolean = {
    (l1.reverse == l2.reverse) ==> (l1 == l2) because {
      check {(l1.reverse == l2.reverse) ==> (l1.reverse.reverse == l2.reverse.reverse) because {reverseSameHelper1(l1.reverse,l2.reverse)}} &&
      check {(l1.reverse.reverse == l2.reverse.reverse) == (l1 == l2) because {ListSpecs.reverseReverse(l1) && ListSpecs.reverseReverse(l2)}}
    }
  }.holds

  //true because  (A ==> B and B ==> A) ==> (A == B)
  def reverseSame[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 == l2) == (l1.reverse == l2.reverse) because {reverseSameHelper1(l1,l2) && reverseSameHelper2(l1,l2)}
  }.holds

  //if the same item is snocced to equal lists, the result will be equal
  def snocToSame[T](l1: List[T], l2: List[T], x: T): Boolean = {
    (l1 == l2) == (l1:+x == l2:+x) because {
      (l1:+x == l2:+x)                      ==| reverseSame(l1:+x,l2:+x)    |
      ((l1:+x).reverse == (l2:+x).reverse)  ==| ListSpecs.snocReverse(l1,x) |
      (x::(l1.reverse) == (l2:+x).reverse)  ==| ListSpecs.snocReverse(l2,x) |
      (x::(l1.reverse) == x::(l2.reverse))  ==| trivial                     |
      ((l1.reverse) == (l2.reverse))        ==| reverseSame(l1,l2)          |
      (l1 == l2)
    }.qed
  }.holds

  //If a list does not contain an item, removing this item yields the same list
  def notContainsRemove[T](l: List[T], x: T): Boolean = {
    require(!l.contains(x))
    l == l-x because {
      l match {
        case Nil() => true
        case y::ys => {
          y::ys     ==| notContainsRemove(ys,x) |
          y::(ys-x) ==| !(y==x)                 |
          (y::ys)-x
        }.qed
      }
    }
  }.holds

  // If list does not contain an item, and we prepend an item to it,
  // and later remove, we get back the original list
  def prependAndRemoveNotContaining[T](x: T, l: List[T]): Boolean = {
    require(!l.contains(x))
    l == (x::l)-x
  }.holds because {
    notContainsRemove(l,x)
  }
}
