import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._
import ListSpecsExt._

object Language {
  @induct
  def cancelLeft[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    require((l1 ++ l2) == (l1 ++ l3))
    l2 == l3
  }.holds

  def cancelRight[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    require((l2 ++ l1) == (l3 ++ l1))
    l2 == l3 because {
      l1 match {
        case Nil () => true
        case x::xs => {
          check {((l2 ++ (x::xs)) == (l3 ++ (x::xs))) == (((l2:+x) ++ xs) == (l3 ++ (x::xs))) because {snocGoesHead(l2,x,xs)}} &&
          check {(((l2:+x) ++ xs) == (l3 ++ (x::xs))) == (((l2:+x) ++ xs) == ((l3:+x) ++ xs)) because {snocGoesHead(l3,x,xs)}} &&
          check {(((l2:+x) ++ xs) == ((l3:+x) ++ xs)) == ((l2:+x) == (l3:+x)) because {cancelRight(xs, l2:+x, l3:+x)}} &&
          check {((l2:+x) == (l3:+x)) == ((l2) == (l3)) because {snocToSame(l2,l3,x)}}
        }.qed
      }
    }
  }.holds

  /*
  Unfortunately, in this case, the recursive call's precondition is not proved to be true
  def cancelRight[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    require((l2 ++ l1) == (l3 ++ l1))
    l2 == l3 because {
      l1 match {
        case Nil () => true
        case x::xs => {
          ((l2 ++ (x::xs)) == (l3 ++ (x::xs)))  ==| snocGoesHead(l2,x,xs)         |
          (((l2:+x) ++ xs) == (l3 ++ (x::xs)))  ==| snocGoesHead(l3,x,xs)         |
          (((l2:+x) ++ xs) == ((l3:+x) ++ xs))  ==| cancelRight(xs, l2:+x, l3:+x) |
          ((l2:+x) == (l3:+x))                  ==| snocToSame(l2,l3,x)           |
          l2 == l3
        }.qed
      }
    }
  }.holds
  */

}
