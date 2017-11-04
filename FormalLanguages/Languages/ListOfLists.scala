import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

//import DoubleReverseCombineList._


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
  }.ensuring {res: List[List[T]] => res.size == l.size &&
    !l.isEmpty ==> res.contains(l.head ++ suffix)}

  def prependToAll[T](prefix: List[T], l: List[List[T]]): List[List[T]] = l match {
    case Nil() => Nil[List[T]]()
    case x :: xs => (prefix ++ x) :: prependToAll(prefix, xs)
  }

  def reverseAll[T](l: List[List[T]]): List[List[T]] ={
    l match {
      case Nil() => Nil[List[T]]
      case Cons(x,xs) => x.reverse :: reverseAll(xs)
    }
  }.ensuring {res => res.size == l.size}

  def prependToAllMap[T](prefix: List[T], l: List[List[T]]): List[List[T]] = appendToAll(l.map(lst => lst.reverse) , prefix.reverse).map(lst => lst.reverse)

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


  def prependToAllLemmaMap[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAllMap(prefix,l) == appendToAll(l.map(lst => lst.reverse) , prefix.reverse).map(lst => lst.reverse)
  }.holds

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
      check {reverseAll(l1) ++ reverseAll(l2) ++ reverseAll(l3) == reverseAll(l1 ++ l2) ++ reverseAll(l3) because {reverseAllConcat(l1,l2)}} &&
      check {reverseAll(l1 ++ l2) ++ reverseAll(l3) == reverseAll(l1 ++ l2 ++ l3) because {reverseAllConcat(l1++l2,l3)}}
    }
  }.holds

  //Idea: High oder proof -> if g(f(a), f(b)) == f(g(a,b)) then g(f(a), g(f(b), f(c))) == f(g(a, g(b,c)))
  def reverseAllConcat4[T](l1:List[List[T]], l2:List[List[T]], l3:List[List[T]], l4:List[List[T]]): Boolean = {
    reverseAll(l1) ++ reverseAll(l2) ++ reverseAll(l3) ++ reverseAll(l4) == reverseAll(l1 ++ l2 ++ l3 ++ l4) because {
    check {reverseAll(l1) ++ reverseAll(l2) ++ reverseAll(l3) ++ reverseAll(l4) == reverseAll(l1 ++ l2) ++ reverseAll(l3) ++ reverseAll(l4) because {reverseAllConcat(l1,l2)}} &&
    check {reverseAll(l1 ++ l2) ++ reverseAll(l3) ++ reverseAll(l4) == reverseAll(l1 ++ l2 ++ l3) ++ reverseAll(l4) because{reverseAllConcat(l1++l2,l3)}} &&
    check {reverseAll(l1 ++ l2 ++ l3) ++ reverseAll(l4) == reverseAll(l1 ++ l2 ++ l3 ++ l4) because {reverseAllConcat(l1++l2++l3, l4)}}
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

  def prependToEmptyList[T](prefix: List[T]): Boolean = {
    prependToAll(prefix, List[List[T]](Nil[T]())) == List(prefix) because {
      prependToAll(prefix, List[List[T]](Nil[T]()))                                                         ==| prependToAllLemma(prefix, List[List[T]](Nil[T]())) |
      reverseAll(appendToAll(reverseAll(List[List[T]](Nil[T]())), prefix.reverse))                          ==| trivial |
      reverseAll(appendToAll(List[List[T]](Nil[T]()),prefix.reverse))                                       ==| trivial |
      reverseAll(List(prefix.reverse))                                                                      ==| trivial |
      List(prefix.reverse.reverse)                                                                          ==| ListSpecs.reverseReverse(prefix) |
      List(prefix)
    }.qed
  }

  def explode[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]): Boolean = {
    decreases(ys.size)
    combineLists(x::xs, y::ys).content == (List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)).content because {
        check {combineLists(x::xs, y::ys).content == (appendToAll(x::xs, y) ++ combineLists(x::xs, ys)).content} &&
        check {(appendToAll(x::xs, y) ++ combineLists(x::xs, ys)).content == (appendToAll(x::xs, y) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content because {combineListDistributiveLeft(x,xs,ys)}} &&
        check {(appendToAll(x::xs, y) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content == ( ((x++y) :: appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content}&&
        check {(((x ++ y) :: appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content == ((List(x ++ y) ++ appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content} &&
        check {((List(x ++ y) ++ appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ combineLists(xs, ys))).content == (((List(x ++ y) ++ appendToAll(xs, y)) ++ prependToAll(x, ys)) ++ combineLists(xs, ys)).content because {ListSpecs.appendAssoc(List(x ++ y) ++ appendToAll(xs, y), prependToAll(x, ys), combineLists(xs, ys))}}
    }
  }.holds

  def doubleReverseCombineList[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    decreases(l2.size)
    combineLists(l1,l2).content == reverseAll(combineLists(reverseAll(l2), reverseAll(l1))).content because {
      l1 match {
        case Nil() => check {combineLists(Nil[List[T]](), l2).content == reverseAll(combineLists(reverseAll(l2), reverseAll(l1))).content}
        case x :: xs => l2 match {
          case Nil() => check {  combineLists(x :: xs,Nil[List[T]]()).content == reverseAll(combineLists(reverseAll(Nil[List[T]]()), reverseAll(x :: xs))).content}
          case y :: ys => {
            check {
              combineLists(x::xs, y::ys).content == (List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)).content
              because {
                explode(x,xs,y,ys)
              }
            } &&
            check {
              (List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)).content ==
              reverseAll(reverseAll((List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)))).content
              because {
                doubleReverseAll((List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)))
              }
            } &&
            check {
              reverseAll(reverseAll((List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ combineLists(xs, ys)))).content ==
              reverseAll(
                reverseAll(List(x ++ y)) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(prependToAll(x,ys)) ++
                reverseAll(combineLists(xs, ys))
              ).content
              because {
                reverseAllConcat4(List(x ++ y), appendToAll(xs,y), prependToAll(x,ys), combineLists(xs, ys))
              }
            } &&
            check {
              reverseAll(
                reverseAll(List(x ++ y)) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(prependToAll(x,ys)) ++
                reverseAll(combineLists(xs, ys))
              ).content ==
              reverseAll(
                reverseAll(List(x ++ y)) ++
                reverseAll(prependToAll(x,ys)) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(combineLists(xs, ys))
              ).content because {
                reverseAllChangeOrder4(
                  reverseAll(List(x ++ y)),
                  reverseAll(appendToAll(xs,y)),
                  reverseAll(prependToAll(x,ys)),
                  reverseAll(combineLists(xs, ys))
                )
              }
            } &&
            check {
              reverseAll(
                reverseAll(List(x ++ y)) ++
                reverseAll(prependToAll(x,ys)) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(combineLists(xs, ys))
              ).content ==
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                reverseAll(prependToAll(x,ys)) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(combineLists(xs, ys))
              ).content
              because {
                ListSpecs.reverseAppend(x,y)
              }
            } &&
            check {
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                reverseAll(prependToAll(x,ys)) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(combineLists(xs, ys))
              ).content ==
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys),x.reverse) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(combineLists(xs, ys))
              ).content
              because {
                reversePrependToAllLemma(x,ys)
              }
            } && check {
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys),x.reverse) ++
                reverseAll(appendToAll(xs,y)) ++
                reverseAll(combineLists(xs, ys))
              ).content ==
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys),x.reverse) ++
                prependToAll(y.reverse,reverseAll(xs)) ++
                reverseAll(combineLists(xs, ys))
              ).content
              because {
                reverseAppendToAllLemma(xs, y)
              }
            } && check {
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys),x.reverse) ++
                prependToAll(y.reverse,reverseAll(xs)) ++
                reverseAll(combineLists(xs, ys))
              ).content ==
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys),x.reverse) ++
                prependToAll(y.reverse,reverseAll(xs)) ++
                combineLists(reverseAll(ys), reverseAll(xs))
              ).content
              because {
                doubleReverseCombineList(xs, ys)
              }
            } && check {
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys),x.reverse) ++
                prependToAll(y.reverse,reverseAll(xs)) ++
                combineLists(reverseAll(xs), reverseAll(ys))
              ).content ==
              reverseAll(combineLists(y.reverse :: reverseAll(ys), x.reverse :: reverseAll(xs))).content
              because {explode(y.reverse, reverseAll(ys), x.reverse, reverseAll(xs))}
            } && check {
              reverseAll(combineLists(y.reverse :: reverseAll(ys), x.reverse :: reverseAll(xs))).content ==
              reverseAll(combineLists(reverseAll(y :: ys), reverseAll(x :: xs))).content
            }
          }
        }
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

  def combineListDistributiveRight[T](l1: List[List[T]], w: List[T], l2: List[List[T]]): Boolean = {
    combineLists(l1, w::l2).content == (appendToAll(l1, w) ++ combineLists(l1, l2)).content
  }.holds

  def combineListDistributiveLeft[T](w: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    decreases(l2.size)
    combineLists(w::l1, l2).content == (prependToAll(w, l2) ++ combineLists(l1, l2)).content because {
      l2 match {
        case Nil() => true
        case _ => {
          combineLists((w ::  l1), l2).content                                                                                      ==| doubleReverseCombineList((w::l1),l2) |
          reverseAll(combineLists(reverseAll(l2), reverseAll((w ::  l1)))).content                                                  ==| trivial |
          reverseAll(combineLists(reverseAll(l2), w.reverse :: reverseAll(l1))).content                                             ==| trivial |
          (reverseAll(appendToAll(reverseAll(l2), w.reverse) ++ combineLists(reverseAll(l2), reverseAll(l1)))).content              ==| reverseAllConcat(appendToAll(reverseAll(l2), w.reverse), combineLists(reverseAll(l2), reverseAll(l1))) |
          (reverseAll(appendToAll(reverseAll(l2), w.reverse)) ++ reverseAll(combineLists(reverseAll(l2), reverseAll(l1)))).content  ==| prependToAllLemma(w,l2) |
          (prependToAll(w, l2) ++ reverseAll(combineLists(reverseAll(l2), reverseAll(l1)))).content                                 ==| doubleReverseCombineList(l1, l2) |
          (prependToAll(w, l2) ++ combineLists(l1, l2)).content
        }.qed
      }
    }
  }.holds

}
