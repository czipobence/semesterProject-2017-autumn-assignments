import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

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
}

import ListSpecsExt._

object ListOfLists {
  def appendToAll[T](l: List[List[T]], suffix: List[T]): List[List[T]] = {
    l match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => (x ++ suffix) :: appendToAll(xs, suffix)
    }
  }.ensuring {res: List[List[T]] => res.size == l.size}

  def prependToAll[T](prefix: List[T], l: List[List[T]]): List[List[T]] = {
    l match {
      case Nil() => Nil[List[T]]()
      case x :: xs => (prefix ++ x) :: prependToAll(prefix, xs)
    }
  }

  def reverseAll[T](l: List[List[T]]): List[List[T]] ={
    l match {
      case Nil() => Nil[List[T]]
      case Cons(x,xs) => x.reverse :: reverseAll(xs)
    }
  }.ensuring {res => res.size == l.size}

  //@ignore
  def combineLists[T](thisList: List[List[T]], thatList: List[List[T]]): List[List[T]] = {
    thatList match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => appendToAll(thisList, x) ++ combineLists(thisList, xs)
    }
  }.ensuring {res: List[List[T]] => res.size == thisList.size * thatList.size}

}

import ListOfLists._

object ListOfListsSpecs {

  def prependToAllLemma[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAll(prefix,l) == reverseAll(appendToAll(reverseAll(l) , prefix.reverse)) because {
      l match {
        case Nil() => true
        case x :: xs => {
          prependToAll(prefix,x::xs)                                                                                      ==| trivial |
          (prefix ++ x) :: prependToAll(prefix,xs)                                                                        ==| doubleReverseAll((prefix ++ x) :: prependToAll(prefix,xs)) |
          reverseAll(reverseAll((prefix ++ x) :: prependToAll(prefix,xs)))                                                ==| trivial |
          reverseAll((prefix ++ x).reverse :: reverseAll(prependToAll(prefix,xs)))                                        ==| ListSpecs.reverseAppend(prefix,x) |
          reverseAll((x.reverse ++ prefix.reverse) :: reverseAll(prependToAll(prefix,xs)))                                ==| prependToAllLemma(prefix,xs) |
          reverseAll((x.reverse ++ prefix.reverse) :: reverseAll(reverseAll(appendToAll(reverseAll(xs),prefix.reverse)))) ==| doubleReverseAll(appendToAll(reverseAll(xs),prefix.reverse)) |
          reverseAll((x.reverse ++ prefix.reverse) :: appendToAll(reverseAll(xs),prefix.reverse))                         ==| trivial |
          reverseAll(appendToAll(x.reverse :: reverseAll(xs), prefix.reverse))                                            ==| trivial |
          reverseAll(appendToAll(reverseAll(x::xs), prefix.reverse))
        }.qed
      }
    }
  }.holds

  def reversePrependToAllLemma[T](prefix: List[T], l: List[List[T]]): Boolean = {
    reverseAll(prependToAll(prefix,l)) == appendToAll(reverseAll(l), prefix.reverse) because {
      reverseAll(prependToAll(prefix,l))                                  ==| prependToAllLemma(prefix, l) |
      reverseAll(reverseAll(appendToAll(reverseAll(l), prefix.reverse)))  ==| doubleReverseAll(appendToAll(reverseAll(l), prefix.reverse)) |
      appendToAll(reverseAll(l), prefix.reverse)
    }.qed
  }.holds

  def reverseAppendToAllLemma[T](l: List[List[T]], suffix: List[T]): Boolean = {
    reverseAll(appendToAll(l,suffix)) == prependToAll(suffix.reverse, reverseAll(l)) because {
      reverseAll(appendToAll(l,suffix))                                         ==| doubleReverseAll(l)                               |
      reverseAll(appendToAll(reverseAll(reverseAll(l)),suffix))                 ==| ListSpecs.reverseReverse(suffix)                  |
      reverseAll(appendToAll(reverseAll(reverseAll(l)),suffix.reverse.reverse)) ==| prependToAllLemma(suffix.reverse, reverseAll(l))  |
      prependToAll(suffix.reverse, reverseAll(l))
    }.qed
  }.holds

  //reverseAll for SingleList, actually trivial
  def reverseAllSingleItem[T](list: List[T]): Boolean = {
    reverseAll(List(list)) == List(list.reverse)
  }.holds

  //if we reverse every item in the list twice, it will be the identity operation
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

  def reverseAllConcat[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    reverseAll(l1 ++ l2) == reverseAll(l1) ++ reverseAll(l2) because {
      l2 match {
        case Nil() => true
        case x :: xs => {
          reverseAll(l1) ++ reverseAll(x :: xs)           ==| trivial |
          reverseAll(l1) ++ (x.reverse :: reverseAll(xs)) ==| snocGoesHead(reverseAll(l1), x.reverse, reverseAll(xs)) |
          (reverseAll(l1) :+ x.reverse) ++ reverseAll(xs) ==| reverseAllDistributiveOverSnoc(l1,x) |
          reverseAll(l1 :+ x) ++ reverseAll(xs)           ==| reverseAllConcat(l1 :+ x, xs) |
          reverseAll((l1 :+ x) ++ xs)                     ==| snocGoesHead(l1,x,xs) |
          reverseAll(l1 ++ (x :: xs))
        }.qed
      }
    }
  }.holds


  def reverseAllConcat3[T](l1:List[List[T]], l2:List[List[T]], l3:List[List[T]]): Boolean = {
    reverseAll(l1) ++ reverseAll(l2) ++ reverseAll(l3) == reverseAll(l1 ++ l2 ++ l3) because {
      reverseAll(l1) ++ reverseAll(l2) ++ reverseAll(l3)  ==| reverseAllConcat(l1,l2)     |
      reverseAll(l1 ++ l2) ++ reverseAll(l3)              ==| reverseAllConcat(l1++l2,l3) |
      reverseAll(l1 ++ l2 ++ l3)
    }.qed
  }.holds

  def reverseAllDistributiveOverSnoc[T](l: List[List[T]], t: List[T]): Boolean = { //or name should be the other way around???
    (reverseAll(l) :+ t.reverse) == reverseAll(l :+ t) because {
      l match {
        case Nil() => true
        case x :: xs => reverseAllDistributiveOverSnoc(xs, t)
      }
    }
  }.holds

  def prependToEmptyList[T](prefix: List[T]): Boolean = {
    prependToAll(prefix, List[List[T]](Nil[T]())) == List(prefix) because {
      prependToAll(prefix, List[List[T]](Nil[T]()))                                                         ==| prependToAllLemma(prefix, List[List[T]](Nil[T]())) |
      reverseAll(appendToAll(reverseAll(List[List[T]](Nil[T]())), prefix.reverse))                          ==| trivial |
      reverseAll(appendToAll(List[List[T]](Nil[T]()),prefix.reverse))                                       ==| trivial |
      reverseAll(List(prefix.reverse))                                                                      ==| trivial |
      List(prefix.reverse.reverse)                                                                          ==| ListSpecs.reverseReverse(prefix) |
      List(prefix)
    }.qed
  }.holds

  def explode[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]): Boolean = {
    combineLists(x::xs, y::ys).content == (List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)).content because {
        combineLists(x::xs, y::ys).content                                                              ==| trivial                                                                                               |
        (appendToAll(x::xs, y) ++ combineLists(x::xs, ys)).content                                      ==| combineListDistributiveLeft(x,xs,ys)                                                                  |
        (appendToAll(x::xs, y) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content                ==| (appendToAll(x::xs, y) == ((x ++ y) :: appendToAll(xs, y)))                                           |
        (((x ++ y) :: appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content     ==| ((x ++ y) :: appendToAll(xs, y) == (List(x ++ y) ++ appendToAll(xs, y)))                              |
        ((List(x ++ y) ++ appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content ==| ListSpecs.appendAssoc(List(x ++ y) ++ appendToAll(xs, y), prependToAll(x, ys), combineLists(xs, ys))  |
        (((List(x ++ y) ++ appendToAll(xs, y)) ++ prependToAll(x, ys)) ++ combineLists(xs, ys)).content
    }.qed
  }.holds

  def doubleReverseCombineList[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    decreases(l1.size)
    combineLists(l1,l2).content == reverseAll(combineLists(reverseAll(l2), reverseAll(l1))).content because {
      l1 match {
        case Nil() => check {combineLists(Nil[List[T]](), l2).content == reverseAll(combineLists(reverseAll(l2), reverseAll(l1))).content}
        case x :: xs => {
          combineLists(x :: xs,l2).content                                                                                        ==| combineListDistributiveLeft(x,xs,l2) |
          (prependToAll(x,l2) ++ combineLists(xs, l2)).content                                                                    ==| prependToAllLemma(x,l2) |
          (reverseAll(appendToAll(reverseAll(l2),x.reverse)) ++ combineLists(xs, l2)).content                                     ==| doubleReverseCombineList(xs,l2) |
          (reverseAll(appendToAll(reverseAll(l2),x.reverse)) ++ reverseAll(combineLists(reverseAll(l2),reverseAll(xs)))).content  ==| reverseAllConcat(appendToAll(reverseAll(l2),x.reverse),combineLists(reverseAll(l2),reverseAll(xs))) |
          reverseAll(appendToAll(reverseAll(l2),x.reverse) ++ combineLists(reverseAll(l2),reverseAll(xs))).content                ==| trivial |
          reverseAll(combineLists(reverseAll(l2),x.reverse :: reverseAll(xs))).content                                            ==| trivial |
          reverseAll(combineLists(reverseAll(l2),reverseAll(x::xs))).content
        }.qed
      }
    }
  }.holds

  def reverseAllChangeOrder[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    reverseAll(l1 ++ l2).content == reverseAll(l2 ++ l1).content because {
      reverseAll(l1 ++ l2).content               ==| reverseAllConcat(l1,l2)  |
      (reverseAll(l1) ++ reverseAll(l2)).content ==| trivial                  |
      (reverseAll(l2) ++ reverseAll(l1)).content ==| reverseAllConcat(l2,l1)  |
      reverseAll(l2 ++ l1).content
    }.qed
  }.holds

  def reverseAllChangeOrder4[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]], l4: List[List[T]]): Boolean = {
    reverseAll(l1 ++ l2 ++ l3 ++ l4).content == reverseAll(l1 ++ l3 ++ l2 ++ l4).content because {
       reverseAll(l1 ++ l2 ++ l3 ++ l4).content                           ==| ListSpecs.appendAssoc(l1, l2, l3) |
       reverseAll(l1 ++ (l2 ++ l3) ++ l4).content                         ==| reverseAllConcat3(l1, l2++l3, l4) |
       (reverseAll(l1) ++ reverseAll(l2 ++ l3) ++ reverseAll(l4)).content ==| reverseAllChangeOrder(l2,l3)      |
       (reverseAll(l1) ++ reverseAll(l2 ++ l3) ++ reverseAll(l4)).content ==| reverseAllConcat3(l1, l3++l2, l4) |
       reverseAll(l1 ++ (l3 ++ l2) ++ l4).content                         ==| ListSpecs.appendAssoc(l1, l3, l2) |
       reverseAll(l1 ++ l3 ++ l2 ++ l4).content
    }.qed
  }.holds

  def combineListAssoc[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    combineLists(combineLists(l1,l2),l3).content == combineLists(l1, combineLists(l2,l3)).content because {
      check {
        (combineLists(combineLists(l1,l2),l3).content == combineLists(l1, combineLists(l2,l3)).content) ==
        forall((x:List[T]) => combineLists(combineLists(l1,l2),l3).contains(x) == combineLists(l1, combineLists(l2,l3)).contains(x))
      }
    }
  }.holds

  def combineListDistributiveRight[T](l1: List[List[T]], w: List[T], l2: List[List[T]]): Boolean = {
    combineLists(l1, w::l2).content == (appendToAll(l1, w) ++ combineLists(l1, l2)).content
  }.holds


  def combineListDistributiveLeft[T](w: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    decreases(l2.size)
    combineLists(w::l1, l2).content == (prependToAll(w, l2) ++ combineLists(l1, l2)).content because {
      l2 match {
        case Nil() => check {  combineLists(w::l1, Nil[List[T]]()).content == (prependToAll(w, Nil[List[T]]()) ++ combineLists(l1, Nil[List[T]]())).content}
        case x :: xs => {
          combineLists(w::l1, x::xs).content                                                            ==| trivial |
          (appendToAll(w::l1, x) ++ combineLists(w::l1, xs)).content                                    ==| trivial |
          (List(w ++ x) ++ appendToAll(l1, x) ++ combineLists(w::l1, xs)).content                       ==| combineListDistributiveLeft(w,l1,xs) |
          (List(w ++ x) ++ appendToAll(l1, x) ++ (prependToAll(w, xs) ++ combineLists(l1,xs))).content  ==| trivial |
          (List(w ++ x) ++ appendToAll(l1, x) ++ prependToAll(w, xs) ++ combineLists(l1,xs)).content    ==| trivial |
          (List(w ++ x) ++ prependToAll(w, xs) ++ appendToAll(l1, x) ++ combineLists(l1,xs)).content    ==| trivial |
          (prependToAll(w, x::xs) ++ appendToAll(l1, x) ++ combineLists(l1,xs)).content                 ==| trivial |
          (prependToAll(w, x::xs) ++ (appendToAll(l1, x) ++ combineLists(l1,xs))).content               ==| trivial |
          (prependToAll(w, x::xs) ++ combineLists(l1,x::xs)).content
        }.qed
      }
    }
  }.holds

}
