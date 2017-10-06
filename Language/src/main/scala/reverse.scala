import stainless.lang._
import stainless.collection._
import stainless.collection.ListSpecs._
import stainless.proof._

object reverse {

  def consRev[T](l: List[T], x: T): Boolean = {
    (x :: l).reverse == l.reverse :+ x
  }.holds

  def appendAddAssoc[T](l1: List[T], l2: List[T], x:T):Boolean = {
    (l1 ++ l2) :+ x == l1 ++ (l2 :+ x)
  }.holds because {
    l1 match {
      case Nil() => true
      case hd :: tail => appendAddAssoc(tail,l2,x)
    }
  }

  def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse
  }.holds because {
    l1 match {
      case Nil() => {
        (Nil() ++ l2).reverse     ==| trivial                               |
        l2.reverse                ==| ListSpecs.rightUnitAppend(l2.reverse) |
        l2.reverse ++ Nil()       ==| trivial                               |
        l2.reverse ++ Nil().reverse
      }.qed
      case x::xs => {
        ((x::xs) ++ l2).reverse         ==| trivial                         |
        (x :: (xs ++ l2)).reverse       ==| consRev[T](xs ++ l2, x)         |
        (xs ++ l2).reverse :+ x         ==| reverseAppend[T](xs,l2)         |
        (l2.reverse ++ xs.reverse) :+ x ==| appendAddAssoc[T](l2.reverse,xs.reverse,x)      |
        l2.reverse ++ (xs.reverse :+ x) ==| consRev[T](xs, x)               |
        l2.reverse ++ (x::xs).reverse
      }.qed
    }
  }
}
