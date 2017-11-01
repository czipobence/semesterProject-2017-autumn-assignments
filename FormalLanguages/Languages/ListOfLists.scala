import stainless.lang._
import stainless.collection._
import stainless.proof._

object ListOfLists {
  def appendToAll[T](l: List[List[T]], suffix: List[T]): List[List[T]] = {
    l match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => (x ++ suffix) :: appendToAll(xs, suffix)
    }
  }.ensuring {res: List[List[T]] => res.size == l.size &&
    !l.isEmpty ==> res.contains(l.head ++ suffix)}

  def prependToAll[T](prefix: List[T], l: List[List[T]]): List[List[T]] = reverseAll(appendToAll(reverseAll(l) , prefix.reverse))

  def reverseAll[T](l: List[List[T]]): List[List[T]] = l match {
    case Nil() => Nil[List[T]]
    case Cons(x,xs) => x.reverse :: reverseAll(xs)
  }

  def prependToAllMap[T](prefix: List[T], l: List[List[T]]): List[List[T]] = appendToAll(l.map(lst => lst.reverse) , prefix.reverse).map(lst => lst.reverse)

  def combineLists[T](thisList: List[List[T]], thatList: List[List[T]]): List[List[T]] = {
    thatList match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => appendToAll(thisList, x) ++ combineLists(thisList, xs)
    }
  }.ensuring {res: List[List[T]] => res.size == thisList.size * thatList.size}
}

import ListOfLists._

object ListOfListsSpecs {

  def prependToAllLemmaMap[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAllMap(prefix,l) == appendToAll(l.map(lst => lst.reverse) , prefix.reverse).map(lst => lst.reverse)
  }.holds

  def prependToAllLemma[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAll(prefix,l) == reverseAll(appendToAll(reverseAll(l) , prefix.reverse))
  }.holds

  //reverseAll for SingleList, actually trivial
  def reverseAllSingleItem[T](list: List[T]): Boolean = {
    reverseAll(List(list)) == List(list.reverse)
  }.holds

  def doubleReverseAll[T](l: List[List[T]]): Boolean = {
    reverseAll(reverseAll(l)) == l because {
      l match {
        case Nil() => true
        case x :: xs => {
          x.reverse.reverse :: reverseAll(reverseAll(xs)) ==| ListSpecs.reverseReverse(x) |
          x :: reverseAll(reverseAll(xs))                 ==| doubleReverseAll(xs)        |
          x :: xs
        }.qed
      }
    }
  }.holds

  def doubleReverseCombineList[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    combineLists(l1,l2) == reverseAll(combineLists(reverseAll(l2), reverseAll(l1))) because {
      l2 match {
        case Nil() => true
        case y::ys => l1 match {
          case Nil() => true
          case x::xs => {
            check{(combineLists(x::xs,y::ys)) == (appendToAll(x::xs, y) ++ combineLists(x::xs, ys))} &&
            check{(appendToAll(x::xs, y) ++ combineLists(x::xs, ys)) == (appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(x::xs))))}  &&
            check{(appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(x::xs)))) == (appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), x.reverse :: reverseAll(xs))))}  &&
            check{(appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), x.reverse :: reverseAll(xs)))) == (appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse) ++ combineLists(reverseAll(ys), reverseAll(xs))))}  &&
            check{(appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse) ++ combineLists(reverseAll(ys), reverseAll(xs)))) == (appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs))))}  &&
            check{(appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))) == ((x ++ y) :: (appendToAll(xs, y)) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs))))}
          }
        }
      }

    }
  }.holds

  def reverseAllConcat[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    reverseAll(l1 ++ l2) == reverseAll(l1) ++ reverseAll(l2) because {
      l2 match {
        case Nil() => true
        case x :: xs => {
          check {(reverseAll(l1) ++ reverseAll(x :: xs)) == (reverseAll(l1) ++ (x.reverse :: reverseAll(xs)))} &&
          check {(reverseAll(l1) ++ (x.reverse :: reverseAll(xs))) == ((reverseAll(l1) :+ x.reverse) ++ reverseAll(xs)) because {snocGoesHead(reverseAll(l1), x.reverse, reverseAll(xs))}} &&
          check {((reverseAll(l1) :+ x.reverse) ++ reverseAll(xs)) == (reverseAll(l1 :+ x) ++ reverseAll(xs)) because{reverseAllDistributiveOverSnoc(l1,x)}} &&
          check {(reverseAll(l1 :+ x) ++ reverseAll(xs)) == (reverseAll((l1 :+ x) ++ xs)) because {reverseAllConcat(l1 :+ x, xs)}} &&
          check {(reverseAll((l1 :+ x) ++ xs)) == (reverseAll(l1 ++ (x :: xs))) because {snocGoesHead(l1,x,xs)}}
        }
      }
    }
  }.holds

  def reverseAllDistributiveOverSnoc[T](l: List[List[T]], t: List[T]): Boolean = { //or name should be the other way around???
    (reverseAll(l) :+ t.reverse) == reverseAll(l :+ t) because {
      l match {
        case Nil() => true
        case x :: xs => reverseAllDistributiveOverSnoc(xs, t)
      }
    }
  }.holds

  def snocGoesHead[T](l1: List[T], x: T,l2: List[T]) : Boolean = {
    ((l1 :+ x) ++ l2) == (l1 ++ (x :: l2)) because {
      check {((l1 :+ x) ++ l2) == ((l1 ++ Cons[T](x, Nil())) ++ l2) because {ListSpecs.snocIsAppend(l1,x)}} &&
      check {((l1 ++ Cons[T](x, Nil())) ++ l2) == (l1 ++ (Cons[T](x, Nil()) ++ l2)) because {ListSpecs.appendAssoc(l1, Cons[T](x, Nil()), l2)}} &&
      check {(l1 ++ (Cons[T](x, Nil()) ++ l2)) == (l1 ++ (x :: l2))}
    }
  }.holds

  def combineDistributiveLeftHelper2[T](w: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
      combineLists((w ::  l1), l2).content == (prependToAll(w, l2) ++ combineLists(l1, l2)).content
  }.holds

  def combineDistributiveLeftHelper[T](w: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    combineLists((w ::  l1), l2) == prependToAll(w, l2) ++ combineLists(l1, l2) because {
      combineLists((w ::  l1), l2)                                                                                    ==| doubleReverseCombineList((w::l1),l2) |
      reverseAll(combineLists(reverseAll(l2), reverseAll((w ::  l1))))                                                ==| trivial |
      reverseAll(combineLists(reverseAll(l2), w.reverse :: reverseAll(l1)))                                           ==| trivial |
      reverseAll(appendToAll(reverseAll(l2), w.reverse) ++ combineLists(reverseAll(l2), reverseAll(l1)))              ==| reverseAllConcat(appendToAll(reverseAll(l2), w.reverse), combineLists(reverseAll(l2), reverseAll(l1))) |
      reverseAll(appendToAll(reverseAll(l2), w.reverse)) ++ reverseAll(combineLists(reverseAll(l2), reverseAll(l1)))  ==| trivial |
      prependToAll(w, l2) ++ reverseAll(combineLists(reverseAll(l2), reverseAll(l1)))                                 ==| doubleReverseCombineList(l1, l2) |
      prependToAll(w, l2) ++ combineLists(l1, l2)
    }.qed
  }.holds

}
