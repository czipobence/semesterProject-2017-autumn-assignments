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
  }.ensuring {res: List[List[T]] => res.size == l.size &&
    !l.isEmpty ==> res.contains(l.head ++ suffix)}

  def prependToAll[T](prefix: List[T], l: List[List[T]]): List[List[T]] = reverseAll(appendToAll(reverseAll(l) , prefix.reverse))

  def reverseAll[T](l: List[List[T]]): List[List[T]] = l match {
    case Nil() => Nil[List[T]]
    case Cons(x,xs) => x.reverse :: reverseAll(xs)
  }

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
    prependToAll(prefix,l) == reverseAll(appendToAll(reverseAll(l) , prefix.reverse))
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

  //Question: If the function is too long, it just can't verify even trivial steps
  def doubleReverseCombineList[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    combineLists(l1,l2).content == reverseAll(combineLists(reverseAll(l2), reverseAll(l1))).content because {
      l2 match {
        case Nil() => true
        case y::ys => l1 match {
          case Nil() => true
          case x::xs => {
            check{
              combineLists(x::xs,y::ys).content ==
                 (
                   ((x ++ y) :: (appendToAll(xs, y))) ++
                   reverseAll(
                     appendToAll(reverseAll(ys), x.reverse)
                   ) ++
                   reverseAll(
                     combineLists(reverseAll(ys), reverseAll(xs))
                   )
                 ).content because {
                   doubleReverseCombineListPt1(x,xs,y,ys)
                 }
            }  &&
            check{
              (
                ((x ++ y) :: (appendToAll(xs, y))) ++
                reverseAll(
                  appendToAll(reverseAll(ys), x.reverse)
                ) ++
                reverseAll(
                  combineLists(reverseAll(ys), reverseAll(xs))
                )
              ).content ==
              (
                reverseAll(
                  List(y.reverse ++ x.reverse) ++
                  appendToAll(reverseAll(ys), x.reverse) ++
                  reverseAll(appendToAll(xs, y)) ++
                  combineLists(reverseAll(ys), reverseAll(xs))
                )
              ).content because {
                doubleReverseCombineListPt2(x,xs,y,ys)
              }
            } &&
            check {
              reverseAll(
                List(y.reverse ++ x.reverse) ++
                appendToAll(reverseAll(ys), x.reverse) ++
                reverseAll(appendToAll(xs, y)) ++
                combineLists(reverseAll(ys), reverseAll(xs))
              ).content ==
              (
                reverseAll(
                  appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
                  reverseAll(
                    combineLists(xs, y::ys)
                  )
                )
              ).content
               because {
                doubleReverseCombineListPt3(x,xs,y,ys)
              }
            }
            check {
              (
                reverseAll(
                  appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
                  reverseAll(
                    combineLists(xs, y::ys)
                  )
                )
              ).content ==
              reverseAll(combineLists(reverseAll(y::ys), reverseAll(x::xs))).content because {
                doubleReverseCombineListPt4(x,xs,y,ys)
              }
            }
          }
        }
      }
    }
  }.holds

  def doubleReverseCombineListPt1[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]):Boolean = {
    combineLists(x::xs,y::ys).content == (((x ++ y) :: (appendToAll(xs, y))) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))).content because {
      check{
        combineLists(x::xs,y::ys).content == (appendToAll(x::xs, y) ++ combineLists(x::xs, ys)).content
      } &&
      check{
        (appendToAll(x::xs, y) ++ combineLists(x::xs, ys)).content ==
        (appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(x::xs)))).content because {
          doubleReverseCombineList(x::xs, ys)
        }
      }  &&
      check{
        (appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(x::xs)))).content ==
          (appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), x.reverse :: reverseAll(xs)))).content
      }  &&
      check{
        (appendToAll(x::xs, y) ++ reverseAll(combineLists(reverseAll(ys), x.reverse :: reverseAll(xs)))).content ==
          (appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse) ++ combineLists(reverseAll(ys), reverseAll(xs)))).content
      }  &&
      check{
        (appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse) ++ combineLists(reverseAll(ys), reverseAll(xs)))).content ==
          (appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))).content because {
            reverseAllConcat(appendToAll(reverseAll(ys), x.reverse), combineLists(reverseAll(ys), reverseAll(xs)))
          }
      }  &&
      check{
        (appendToAll(x::xs, y) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))).content ==
           (((x ++ y) :: (appendToAll(xs, y))) ++ reverseAll(appendToAll(reverseAll(ys), x.reverse)) ++ reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))).content
      }
    }

  }.holds


  def doubleReverseCombineListPt2[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]): Boolean = {
    (
      ((x ++ y) :: (appendToAll(xs, y))) ++
      reverseAll(
        appendToAll(reverseAll(ys), x.reverse)
      ) ++
      reverseAll(
        combineLists(reverseAll(ys), reverseAll(xs))
      )
    ).content ==
    (
      reverseAll(
        List(y.reverse ++ x.reverse) ++
        appendToAll(reverseAll(ys), x.reverse) ++
        reverseAll(appendToAll(xs, y)) ++
        combineLists(reverseAll(ys), reverseAll(xs))
      )
    ).content because {
      check{
        (
          ((x ++ y) :: (appendToAll(xs, y))) ++
          reverseAll(
            appendToAll(reverseAll(ys), x.reverse)
          ) ++
          reverseAll(
            combineLists(reverseAll(ys), reverseAll(xs))
          )
        ).content ==
        (
          reverseAll(
            List(y.reverse ++ x.reverse)
          ) ++
          reverseAll(
            reverseAll(appendToAll(xs, y))
          ) ++
          reverseAll(
            appendToAll(reverseAll(ys), x.reverse)
          ) ++
          reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))
        ).content because {
          doubleReverseAppendConsLemma(x,y,appendToAll(xs, y))
        }
      } &&
      check {
        (
          reverseAll(
            List(y.reverse ++ x.reverse)
          ) ++
          reverseAll(
            reverseAll(appendToAll(xs, y))
          ) ++
          reverseAll(
            appendToAll(reverseAll(ys), x.reverse)
          ) ++
          reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))
        ).content ==
        (
          reverseAll(
            List(y.reverse ++ x.reverse)
          ) ++
          reverseAll(
            appendToAll(reverseAll(ys), x.reverse)
          ) ++
          reverseAll(
            reverseAll(appendToAll(xs, y))
          ) ++
          reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))
        ).content
      } &&
      check {
        (
          reverseAll(
            List(y.reverse ++ x.reverse)
          ) ++
          reverseAll(
            appendToAll(reverseAll(ys), x.reverse)
          ) ++
          reverseAll(
            reverseAll(appendToAll(xs, y))
          ) ++
          reverseAll(combineLists(reverseAll(ys), reverseAll(xs)))
        ).content ==
        (
          reverseAll(
            List(y.reverse ++ x.reverse) ++
            appendToAll(reverseAll(ys), x.reverse) ++
            reverseAll(appendToAll(xs, y)) ++
            combineLists(reverseAll(ys), reverseAll(xs))
          )
        ).content because {
          reverseAllConcat4(
            List(y.reverse ++ x.reverse),
            appendToAll(reverseAll(ys), x.reverse),
            reverseAll(appendToAll(xs, y)),
            combineLists(reverseAll(ys), reverseAll(xs))
          )
        }
      }
    }
  }.holds

  def doubleReverseCombineListPt3[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]): Boolean = {
    reverseAll(
      List(y.reverse ++ x.reverse) ++
      appendToAll(reverseAll(ys), x.reverse) ++
      reverseAll(appendToAll(xs, y)) ++
      combineLists(reverseAll(ys), reverseAll(xs))
    ).content ==
    (
      reverseAll(
        appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
        reverseAll(
          combineLists(xs, y::ys)
        )
      )
    ).content because {
      check {
        (
          reverseAll(
            List(y.reverse ++ x.reverse) ++
            appendToAll(reverseAll(ys), x.reverse) ++
            reverseAll(appendToAll(xs, y)) ++
            combineLists(reverseAll(ys), reverseAll(xs))
          )
        ).content ==
        (
          reverseAll(
            (List(y.reverse ++ x.reverse) ++
            appendToAll(reverseAll(ys), x.reverse)) ++
            ((reverseAll(appendToAll(xs, y))) ++
            combineLists(reverseAll(ys), reverseAll(xs)))
          )
        ).content because {
          ListSpecs.appendAssoc(
            List(y.reverse ++ x.reverse) ++ appendToAll(reverseAll(ys), x.reverse),
            reverseAll(appendToAll(xs, y)),
            combineLists(reverseAll(ys), reverseAll(xs))
          )
        }
      } &&
      check {
        (
          reverseAll(
            (List(y.reverse ++ x.reverse) ++
            appendToAll(reverseAll(ys), x.reverse)) ++
            ((reverseAll(appendToAll(xs, y))) ++
            combineLists(reverseAll(ys), reverseAll(xs)))
          )
        ).content ==
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            ((reverseAll(appendToAll(xs, y))) ++
            combineLists(reverseAll(ys), reverseAll(xs)))
          )
        ).content
      } &&
      check {
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            ((reverseAll(appendToAll(xs, y))) ++
            combineLists(reverseAll(ys), reverseAll(xs)))
          )
        ).content ==
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            ((reverseAll(appendToAll(xs, y))) ++
            reverseAll(combineLists(reverseAll(reverseAll(xs)), reverseAll(reverseAll(ys)))))
          )
        ).content because {
          doubleReverseCombineList(reverseAll(ys),reverseAll(xs))
        }
      } &&
      check {
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            ((reverseAll(appendToAll(xs, y))) ++
            reverseAll(combineLists(reverseAll(reverseAll(xs)), reverseAll(reverseAll(ys)))))
          )
        ).content ==
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            (
              reverseAll(appendToAll(xs, y)) ++
              reverseAll(combineLists(xs, ys))
            )
          )
        ).content because {
          doubleReverseAll(xs) && doubleReverseAll(ys)
        }
      } &&
      check {
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            (
              reverseAll(appendToAll(xs, y)) ++
              reverseAll(combineLists(xs, ys))
            )
          )
        ).content ==
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            reverseAll(
              appendToAll(xs, y) ++
              combineLists(xs, ys)
            )
          )
        ).content because {
          reverseAllConcat(appendToAll(xs, y), combineLists(xs, ys))
        }
      } &&
      check {
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            reverseAll(
              appendToAll(xs, y) ++
              combineLists(xs, ys)
            )
          )
        ).content ==
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            reverseAll(
              combineLists(xs, y::ys)
            )
          )
        ).content
      }
    }
  }.holds

  def doubleReverseCombineListPt4[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]): Boolean = {
    (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++ reverseAll(combineLists(xs, y::ys)))).content ==
    (reverseAll(combineLists(reverseAll(y::ys), reverseAll(x::xs)))).content
    because {
      check {
        (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++ reverseAll(combineLists(xs, y::ys)))).content ==
        (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++ reverseAll(reverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))))).content because {
              check {
                (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++ reverseAll(combineLists(xs, y::ys)))).content ==
                (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse)) ++ reverseAll(reverseAll(combineLists(xs, y::ys)))).content because {
                     reverseAllConcat(appendToAll(y.reverse :: reverseAll(ys), x.reverse), reverseAll(combineLists(xs, y::ys)))
                   }
                 } &&
              check {
                (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse)) ++ reverseAll(reverseAll(combineLists(xs, y::ys)))).content ==
                (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse)) ++ reverseAll(reverseAll(reverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))))).content
                because {
                  doubleReverseCombineList(xs, y::ys)
                }
              } &&
              check {
                (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse)) ++ reverseAll(reverseAll(reverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))))).content ==
                (reverseAll(appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++ reverseAll(reverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))))).content
                because {
                    reverseAllConcat(appendToAll(y.reverse :: reverseAll(ys), x.reverse), reverseAll(reverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))))
                }
              }
            }
      } &&
      check {
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            reverseAll(
              reverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))
            )
          )
        ).content ==
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            combineLists(reverseAll(y::ys), reverseAll(xs))
          )
        ).content because {
          doubleReverseAll(combineLists(reverseAll(y::ys), reverseAll(xs)))
        }
      } &&
      check {
        (
          reverseAll(
            appendToAll(y.reverse :: reverseAll(ys), x.reverse) ++
            combineLists(reverseAll(y::ys), reverseAll(xs))
          )
        ).content  ==
        (
          reverseAll(
            appendToAll(reverseAll(y::ys), x.reverse) ++
            combineLists(reverseAll(y::ys), reverseAll(xs))
          )
        ).content
      } &&
      check {
        (
          reverseAll(
            appendToAll(reverseAll(y::ys), x.reverse) ++
            combineLists(reverseAll(y::ys), reverseAll(xs))
          )
        ).content  ==
        (
          reverseAll(
            combineLists(reverseAll(y::ys), x.reverse :: reverseAll(xs))
          )
        ).content
      } &&
      check {
        (
          reverseAll(
            combineLists(reverseAll(y::ys), x.reverse :: reverseAll(xs))
          )
        ).content  ==
        (reverseAll(combineLists(reverseAll(y::ys), reverseAll(x::xs)))).content
      }
    }
  }.holds

  def doubleReverseCombineListHelper1[T](l: List[List[T]], x: List[List[T]], y: List[List[T]]): Boolean = {
    (reverseAll(l  ++ reverseAll(combineLists(x, y)))).content ==
    (reverseAll(l ++ reverseAll(reverseAll(combineLists(reverseAll(y), reverseAll(x)))))).content
    because {
      check {
        (reverseAll(l  ++ reverseAll(combineLists(x, y)))).content ==
           (reverseAll(l)  ++ reverseAll(reverseAll(combineLists(x, y)))).content
           because {
             reverseAllConcat(l, reverseAll(combineLists(x, y)))
           }
         } &&
      check {
        (reverseAll(l)  ++ reverseAll(reverseAll(combineLists(x, y)))).content == (reverseAll(l) ++ reverseAll(reverseAll(reverseAll(combineLists(reverseAll(y), reverseAll(x)))))).content
        because {
          doubleReverseCombineList(x, y)
        }
      } &&
      check {
        (reverseAll(l) ++ reverseAll(reverseAll(reverseAll(combineLists(reverseAll(y), reverseAll(x)))))).content ==
          (reverseAll(l ++ reverseAll(reverseAll(combineLists(reverseAll(y), reverseAll(x)))))).content because {
            reverseAllConcat(l, reverseAll(reverseAll(combineLists(reverseAll(y), reverseAll(x)))))
          }
        }
    }
  }.holds

  def doubleReverseAppendConsLemma[T](x: List[T], y: List[T], l: List[List[T]]):Boolean = {
    (x ++ y) :: l == reverseAll(List(y.reverse ++ x.reverse)) ++ reverseAll(reverseAll(l)) because {
      (x ++ y) :: l                                             ==| doubleReverseAll((x ++ y) :: l) |
      reverseAll(reverseAll((x ++ y) :: l))                     ==| trivial                         |
      reverseAll((x ++ y).reverse :: reverseAll(l))             ==| ListSpecs.reverseAppend(x,y)    |
      reverseAll((y.reverse ++ x.reverse) :: reverseAll(l))     ==| trivial                         |
      reverseAll(List(y.reverse ++ x.reverse) ++ reverseAll(l)) ==| trivial                         |
      reverseAll(List(y.reverse ++ x.reverse)) ++ reverseAll(reverseAll(l))
    }.qed
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


  def combineListDistributiveRight[T](l1: List[List[T]], w: List[T], l2: List[List[T]]): Boolean = {
    combineLists(l1, w::l2).content == (appendToAll(l1, w) ++ combineLists(l1, l2)).content
  }.holds

  def combineListDistributiveLeft[T](w: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    combineLists(w::l1, l2).content == (prependToAll(w, l2) ++ combineLists(l1, l2)).content because {
      combineLists((w ::  l1), l2).content                                                                                      ==| doubleReverseCombineList((w::l1),l2) |
      reverseAll(combineLists(reverseAll(l2), reverseAll((w ::  l1)))).content                                                  ==| trivial |
      reverseAll(combineLists(reverseAll(l2), w.reverse :: reverseAll(l1))).content                                             ==| trivial |
      (reverseAll(appendToAll(reverseAll(l2), w.reverse) ++ combineLists(reverseAll(l2), reverseAll(l1)))).content              ==| reverseAllConcat(appendToAll(reverseAll(l2), w.reverse), combineLists(reverseAll(l2), reverseAll(l1))) |
      (reverseAll(appendToAll(reverseAll(l2), w.reverse)) ++ reverseAll(combineLists(reverseAll(l2), reverseAll(l1)))).content  ==| trivial |
      (prependToAll(w, l2) ++ reverseAll(combineLists(reverseAll(l2), reverseAll(l1)))).content                                 ==| doubleReverseCombineList(l1, l2) |
      (prependToAll(w, l2) ++ combineLists(l1, l2)).content
    }.qed
  }.holds

}
