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
  def concatLists[T](thisList: List[List[T]], thatList: List[List[T]]): List[List[T]] = {
    thatList match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => appendToAll(thisList, x) ++ concatLists(thisList, xs)
    }
  }.ensuring {res: List[List[T]] => res.size == thisList.size * thatList.size}

}

import ListOfLists._

//Theorems and lemmas about the reverse all operation
object ReverseAllSpecs {
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

  //Actually, it can be said for every f: List[List[T]] --> List[List[T]] that
  // f(a ++ b) == f(a) ++ f(b)
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

  //It can be more generally said that for every f: List[List[T]] --> List[List[T]]
  // we have f(a ++ b) == f(b ++ a) if f(a++b) == f(a) ++ f(b)
  def reverseAllChangeOrder[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    reverseAll(l1 ++ l2).content == reverseAll(l2 ++ l1).content because {
      reverseAll(l1 ++ l2).content               ==| reverseAllConcat(l1,l2)  |
      (reverseAll(l1) ++ reverseAll(l2)).content ==| trivial                  |
      (reverseAll(l2) ++ reverseAll(l1)).content ==| reverseAllConcat(l2,l1)  |
      reverseAll(l2 ++ l1).content
    }.qed
  }.holds

  //The 4-way version of the theorem above
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

  //if a double list contains a list, its reversed correspondant contains the reversed list
  def reverseAllContains[T](l1: List[List[T]], x: List[T]): Boolean = {
    require(l1.contains(x))
    reverseAll(l1).contains(x.reverse) because {
      l1 match {
        case Nil() => false
        case y::ys if y == x => true
        case y::ys => check{reverseAllContains(ys,x)}
      }
    }
  }.holds

  //helper lemma for the next one
  def raRemoveAndAdd[T](l: List[List[T]], x: List[T]): Boolean = {
    require(l.contains(x))
    reverseAll(l).content == (x.reverse :: reverseAll(l-x)).content because {
      l match {
        case Nil() => false
        case y::ys if ((x == y) && (ys contains x)) => {
          check {reverseAll(x::ys).content == (x.reverse :: reverseAll(ys)).content} &&
          check {(x.reverse ::reverseAll(ys)).content == (Set(x.reverse) ++ reverseAll(ys).content)} &&
          check {(Set(x.reverse) ++ reverseAll(ys).content) == (Set(x.reverse) ++ (x.reverse :: reverseAll(ys-x)).content) because {raRemoveAndAdd(ys,x)}} &&
          check {(Set(x.reverse) ++ (x.reverse :: reverseAll(ys-x)).content) == (x.reverse :: (x.reverse::reverseAll(ys-x))).content} &&
          check {(x.reverse :: (x.reverse::reverseAll(ys-x))).content == (x.reverse::reverseAll(ys-x)).content} &&
          check {(x.reverse::reverseAll(ys-x)).content == (x.reverse::reverseAll((x::ys)-x)).content}
        }
        case y::ys if (x==y) => {
          check {reverseAll(x::ys).content == (x.reverse ::reverseAll(ys)).content} &&
          check {!ys.contains(x)}
          check {ys == ((x::ys)-x) because {prependAndRemoveNotContaining(x,ys)}} &&
          check {(x.reverse ::reverseAll(ys)).content == (x.reverse ::reverseAll((x::ys)-x)).content}
        }
        case y::ys => {
          check {reverseAll(y::ys).content == (y.reverse :: reverseAll(ys)).content} &&
          check {(y.reverse :: reverseAll(ys)).content == (Set(y.reverse) ++reverseAll(ys).content)} &&
          check {(Set(y.reverse) ++reverseAll(ys).content) == (Set(y.reverse) ++(x.reverse :: reverseAll(ys-x)).content) because {raRemoveAndAdd(ys,x)}} &&
          check {(Set(y.reverse) ++(x.reverse :: reverseAll(ys-x)).content) == (Set(y.reverse) ++ Set(x.reverse) ++ reverseAll(ys-x).content)} &&
          check {(Set(y.reverse) ++ Set(x.reverse) ++ reverseAll(ys-x).content) == (Set(x.reverse) ++ (Set(y.reverse) ++ reverseAll(ys-x).content))} &&
          check {(Set(x.reverse) ++ (Set(y.reverse) ++ reverseAll(ys-x).content)) == (Set(x.reverse) ++ (y.reverse :: reverseAll(ys-x)).content)} &&
          check {(Set(x.reverse) ++ (y.reverse :: reverseAll(ys-x)).content) == (Set(x.reverse) ++ reverseAll(y::(ys-x)).content)} &&
          check {(Set(x.reverse) ++ reverseAll(y::(ys-x)).content) == (Set(x.reverse) ++ reverseAll((y::ys)-x).content)}
        }
      }
    }
  }.holds


  //if two lists of lists have the same content, their reversed correspondant's content are also the same
  def reverseContentEquals[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    require(l1.content == l2.content)
    reverseAll(l1).content == reverseAll(l2).content because {
      l1 match {
        case Nil() => check {reverseAll(l1).content == reverseAll(l2).content}
        case x::xs if xs.contains(x) => {
          check{reverseAll(x::xs).content == (x.reverse :: reverseAll(xs)).content} &&
          check{(x.reverse :: reverseAll(xs)).content == (Set(x.reverse) ++ reverseAll(xs).content)} &&
          check{(Set(x.reverse) ++ reverseAll(xs).content) == (Set(x.reverse) ++ reverseAll(l2).content) because {check{xs.content == l2.content} && reverseContentEquals(xs,l2)}} &&
          check{(Set(x.reverse) ++ reverseAll(l2).content) == (x.reverse :: reverseAll(l2)).content} &&
          check{(x.reverse :: reverseAll(l2)).content == reverseAll(l2).content because {
            check{
              reverseAll(l2).contains(x.reverse) because {
                check{l2.contains(x)} && reverseAllContains(l2,x)
              }
            }
          }}
        }
        case x::xs => {
          check{reverseAll(x::xs).content == (x.reverse :: reverseAll(xs)).content} &&
          check{(x.reverse :: reverseAll(xs)).content == (Set(x.reverse) ++ reverseAll(xs).content)} &&
          check {(Set(x.reverse) ++ reverseAll(xs).content) == (Set(x.reverse) ++ reverseAll(l2-x).content) because {check{xs.content == (l2-x).content} && reverseContentEquals(xs,(l2-x))}} &&
          check {(Set(x.reverse) ++ reverseAll(l2-x).content) == (x.reverse :: reverseAll(l2-x)).content } &&
          check {(x.reverse :: reverseAll(l2-x)).content == reverseAll(l2).content because{raRemoveAndAdd(l2, x)}}
        }
      }
    }
  }.holds
}

import ReverseAllSpecs._

//Theorems about the appendToAll and prependToAll operations
object AppendPrependSpecs {
  def convertPaToAa[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAll(prefix,l) == reverseAll(appendToAll(reverseAll(l) , prefix.reverse)) because {
      l match {
        case Nil() => true
        case x :: xs => {
          prependToAll(prefix,x::xs)                                                                                      ==| trivial |
          (prefix ++ x) :: prependToAll(prefix,xs)                                                                        ==| doubleReverseAll((prefix ++ x) :: prependToAll(prefix,xs)) |
          reverseAll(reverseAll((prefix ++ x) :: prependToAll(prefix,xs)))                                                ==| trivial |
          reverseAll((prefix ++ x).reverse :: reverseAll(prependToAll(prefix,xs)))                                        ==| ListSpecs.reverseAppend(prefix,x) |
          reverseAll((x.reverse ++ prefix.reverse) :: reverseAll(prependToAll(prefix,xs)))                                ==| convertPaToAa(prefix,xs) |
          reverseAll((x.reverse ++ prefix.reverse) :: reverseAll(reverseAll(appendToAll(reverseAll(xs),prefix.reverse)))) ==| doubleReverseAll(appendToAll(reverseAll(xs),prefix.reverse)) |
          reverseAll((x.reverse ++ prefix.reverse) :: appendToAll(reverseAll(xs),prefix.reverse))                         ==| trivial |
          reverseAll(appendToAll(x.reverse :: reverseAll(xs), prefix.reverse))                                            ==| trivial |
          reverseAll(appendToAll(reverseAll(x::xs), prefix.reverse))
        }.qed
      }
    }
  }.holds

  def convertReverseAaToPa[T](l: List[List[T]], suffix: List[T]): Boolean = {
    reverseAll(appendToAll(l,suffix)) == prependToAll(suffix.reverse, reverseAll(l)) because {
      reverseAll(appendToAll(l,suffix))                                         ==| doubleReverseAll(l)                               |
      reverseAll(appendToAll(reverseAll(reverseAll(l)),suffix))                 ==| ListSpecs.reverseReverse(suffix)                  |
      reverseAll(appendToAll(reverseAll(reverseAll(l)),suffix.reverse.reverse)) ==| convertPaToAa(suffix.reverse, reverseAll(l))  |
      prependToAll(suffix.reverse, reverseAll(l))
    }.qed
  }.holds


  def convertReversePaToAa[T](prefix: List[T], l: List[List[T]]): Boolean = {
    reverseAll(prependToAll(prefix,l)) == appendToAll(reverseAll(l), prefix.reverse) because {
      reverseAll(prependToAll(prefix,l))                                  ==| convertPaToAa(prefix, l) |
      reverseAll(reverseAll(appendToAll(reverseAll(l), prefix.reverse)))  ==| doubleReverseAll(appendToAll(reverseAll(l), prefix.reverse)) |
      appendToAll(reverseAll(l), prefix.reverse)
    }.qed
  }.holds

  def prependToEmptyList[T](prefix: List[T]): Boolean = {
    prependToAll(prefix, List[List[T]](Nil[T]())) == List(prefix) because {
      prependToAll(prefix, List[List[T]](Nil[T]()))                                                         ==| convertPaToAa(prefix, List[List[T]](Nil[T]())) |
      reverseAll(appendToAll(reverseAll(List[List[T]](Nil[T]())), prefix.reverse))                          ==| trivial |
      reverseAll(appendToAll(List[List[T]](Nil[T]()),prefix.reverse))                                       ==| trivial |
      reverseAll(List(prefix.reverse))                                                                      ==| trivial |
      List(prefix.reverse.reverse)                                                                          ==| ListSpecs.reverseReverse(prefix) |
      List(prefix)
    }.qed
  }.holds

  //prepend to all is distributive over list appending
  def paDistributiveOverAppend[T](prefix: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    prependToAll(prefix, l1) ++ prependToAll(prefix, l2) == prependToAll(prefix, l1 ++ l2) because {
      l1 match {
        case Nil() => true
        case x :: xs => {
          check {(prependToAll(prefix, x::xs) ++ prependToAll(prefix, l2)) == (( (prefix ++ x) :: prependToAll(prefix, xs)) ++ prependToAll(prefix, l2))} &&
          check {(( (prefix ++ x) :: prependToAll(prefix, xs)) ++ prependToAll(prefix, l2)) == (( List(prefix ++ x) ++ prependToAll(prefix, xs)) ++ prependToAll(prefix, l2))} &&
          check {(( List(prefix ++ x) ++ prependToAll(prefix, xs)) ++ prependToAll(prefix, l2)) == (List(prefix ++ x) ++ (prependToAll(prefix, xs) ++ prependToAll(prefix, l2)))} &&
          check {(List(prefix ++ x) ++ (prependToAll(prefix, xs) ++ prependToAll(prefix, l2))) == (List(prefix ++ x) ++ prependToAll(prefix, xs++l2)) because {paDistributiveOverAppend(prefix, xs, l2)}} &&
          check {(List(prefix ++ x) ++ prependToAll(prefix, xs++l2)) == ((prefix ++ x) :: prependToAll(prefix, xs++l2))} &&
          check {((prefix ++ x) :: prependToAll(prefix, xs++l2)) == prependToAll(prefix, x :: (xs++l2))} &&
          check {prependToAll(prefix, x :: (xs++l2)) == prependToAll(prefix, (x :: xs)++l2)}
        }
      }
    }
  }.holds

  //the order of appendToAll and prependToAll can be switched
  def appendPrependOrder[T](prefix: List[T], l: List[List[T]], suffix: List[T]): Boolean = {
    prependToAll(prefix, appendToAll(l, suffix)) == appendToAll(prependToAll(prefix, l), suffix) because {
      l match {
        case Nil() => true
        case x::xs => {
          check {prependToAll(prefix, appendToAll(x::xs, suffix)) == prependToAll(prefix, (x++suffix) :: appendToAll(xs, suffix))} &&
          check {prependToAll(prefix, (x++suffix) :: appendToAll(xs, suffix)) == ((prefix ++ (x++suffix)) :: prependToAll(prefix, appendToAll(xs, suffix)))} &&
          check {((prefix ++ (x++suffix)) :: prependToAll(prefix, appendToAll(xs, suffix))) == ((prefix ++ (x++suffix)) :: appendToAll(prependToAll(prefix, xs), suffix)) because {appendPrependOrder(prefix, xs, suffix)}} &&
          check {((prefix ++ (x++suffix)) :: appendToAll(prependToAll(prefix, xs), suffix)) == (((prefix ++ x)++suffix) :: appendToAll(prependToAll(prefix, xs), suffix)) because {ListSpecs.appendAssoc(prefix,x,suffix)}} &&
          check {(((prefix ++ x)++suffix) :: appendToAll(prependToAll(prefix, xs), suffix)) == appendToAll((prefix ++ x) :: prependToAll(prefix, xs), suffix)} &&
          check {appendToAll((prefix ++ x) :: prependToAll(prefix, xs), suffix) == appendToAll(prependToAll(prefix, x :: xs), suffix)}
        }
      }
    }
  }.holds


  def appendToAllContains[T](l: List[List[T]], s: List[T], x: List[T]): Boolean = {
    require(l.contains(x))
    appendToAll(l,s).contains(x++s) because {
      l match {
        case Nil() => true
        case y::ys if (x == y) => true
        case y::ys => appendToAllContains(ys,s,x) because ys.contains(x)
      }
    }
  }.holds

  //this is just a helper lemma for the next one
  //40-45s
  def aaRemoveAndAdd[T](l:List[List[T]], s: List[T], x: List[T]): Boolean = {
    require(l.contains(x))
    ((x++s) :: appendToAll(l-x,s)).content == appendToAll(l,s).content because {
      l match {
        case Nil() => false
        case y::ys if ((x == y) && (ys contains x)) => {
          check {appendToAll(x::ys,s).content == ((x++s) ::appendToAll(ys,s)).content} &&
          check {((x++s) ::appendToAll(ys,s)).content == (Set((x++s)) ++ appendToAll(ys,s).content)} &&
          check {(Set(x++s) ++ appendToAll(ys,s).content) == (Set(x++s) ++ ((x++s) :: appendToAll(ys-x,s)).content) because {aaRemoveAndAdd(ys,s,x)}} &&
          check {(Set(x++s) ++ ((x++s) :: appendToAll(ys-x,s)).content) == ((x++s) :: ((x++s)::appendToAll(ys-x,s))).content} &&
          check {((x++s) :: ((x++s)::appendToAll(ys-x,s))).content == ((x++s)::appendToAll(ys-x,s)).content} &&
          check {((x++s)::appendToAll(ys-x,s)).content == ((x++s)::appendToAll((x::ys)-x,s)).content}
        }
        case y::ys if (x==y) => {
          check {appendToAll(x::ys,s).content == ((x++s) ::appendToAll(ys,s)).content} &&
          check {!ys.contains(x)}
          check {ys == ((x::ys)-x) because {prependAndRemoveNotContaining(x,ys)}} &&
          check {((x++s) ::appendToAll(ys,s)).content == ((x++s) ::appendToAll((x::ys)-x,s)).content}
        }
        case y::ys => {
          check {appendToAll(y::ys,s).content == ((y++s) :: appendToAll(ys,s)).content} &&
          check {((y++s) :: appendToAll(ys,s)).content == (Set(y++s) ++appendToAll(ys,s).content)} &&
          check {(Set(y++s) ++appendToAll(ys,s).content) == (Set(y++s) ++((x++s) :: appendToAll(ys-x,s)).content) because {aaRemoveAndAdd(ys,s,x)}} &&
          check {(Set(y++s) ++((x++s) :: appendToAll(ys-x,s)).content) == (Set(y++s) ++ Set(x++s) ++ appendToAll(ys-x,s).content)} &&
          check {(Set(y++s) ++ Set(x++s) ++ appendToAll(ys-x,s).content) == (Set(x++s) ++ (Set(y++s) ++ appendToAll(ys-x,s).content))} &&
          check {(Set(x++s) ++ (Set(y++s) ++ appendToAll(ys-x,s).content)) == (Set(x++s) ++ ((y++s) :: appendToAll(ys-x,s)).content)} &&
          check {(Set(x++s) ++ ((y++s) :: appendToAll(ys-x,s)).content) == (Set(x++s) ++ appendToAll(y::(ys-x),s).content)} &&
          check {(Set(x++s) ++ appendToAll(y::(ys-x),s).content) == (Set(x++s) ++ appendToAll((y::ys)-x,s).content)}
        }
      }
    }
  }.holds

  // if two list has the same content then appeding the same item to each of
  // the lists yield lists with same content
  def aaWithContentEquals[T](l1: List[List[T]], l2: List[List[T]], suffix: List[T]): Boolean = {
    require(l1.content == l2.content)
    decreases(l1.size)
    appendToAll(l1, suffix).content == appendToAll(l2,suffix).content because {
      l1 match {
        case Nil() => true
        case x :: xs if xs.contains(x) => {
          check {xs.content == (x::xs).content} &&
          check {appendToAll(x::xs, suffix).content == ( (x++suffix) ::appendToAll(xs,suffix)).content} &&
          check {( (x++suffix) ::appendToAll(xs,suffix)).content == appendToAll(xs,suffix).content because {appendToAllContains(xs,suffix,x)}}
          check {appendToAll(xs,suffix).content == appendToAll(l2,suffix).content because { (xs.content == l2.content) && aaWithContentEquals(xs,l2,suffix)}}
        }
        case x :: xs  => {
          check {appendToAll(x::xs, suffix).content == ((x++suffix) :: appendToAll(xs,suffix)).content} &&
          check {((x++suffix) :: appendToAll(xs,suffix)).content == Set(x++suffix) ++ appendToAll(xs,suffix).content} &&
          check {Set(x++suffix) ++ appendToAll(xs,suffix).content ==  Set(x++suffix) ++ appendToAll(l2-x,suffix).content because {aaWithContentEquals(xs, l2-x, suffix)}} &&
          check {Set(x++suffix) ++ appendToAll(l2-x,suffix).content == ((x++suffix) :: appendToAll(l2-x,suffix)).content} &&
          check {((x++suffix) :: appendToAll(l2-x,suffix)).content == appendToAll(l2,suffix).content because {aaRemoveAndAdd(l2,suffix,x)}}
        }
      }
    }
  }.holds
}

import AppendPrependSpecs._

//Theorems about the concatLists operation
object ConcatListsSpecs {


  def clInductRight[T](l1: List[List[T]], w: List[T], l2: List[List[T]]): Boolean = {
    concatLists(l1, w::l2).content == (appendToAll(l1, w) ++ concatLists(l1, l2)).content
  }.holds


  def clInductLeft[T](w: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    decreases(l2.size)
    concatLists(w::l1, l2).content == (prependToAll(w, l2) ++ concatLists(l1, l2)).content because {
      l2 match {
        case Nil() => check {  concatLists(w::l1, Nil[List[T]]()).content == (prependToAll(w, Nil[List[T]]()) ++ concatLists(l1, Nil[List[T]]())).content}
        case x :: xs => {
          /*concatLists(w::l1, x::xs).content                                                            ==| trivial |
          (appendToAll(w::l1, x) ++ concatLists(w::l1, xs)).content                                    ==| trivial |*/
          (List(w ++ x) ++ appendToAll(l1, x) ++ concatLists(w::l1, xs)).content                       ==| clInductLeft(w,l1,xs) |
          (List(w ++ x) ++ appendToAll(l1, x) ++ (prependToAll(w, xs) ++ concatLists(l1,xs))).content  ==| trivial |
          (List(w ++ x) ++ appendToAll(l1, x) ++ prependToAll(w, xs) ++ concatLists(l1,xs)).content    ==| trivial |
          (List(w ++ x) ++ prependToAll(w, xs) ++ appendToAll(l1, x) ++ concatLists(l1,xs)).content    ==| trivial |
          (prependToAll(w, x::xs) ++ appendToAll(l1, x) ++ concatLists(l1,xs)).content                 ==| trivial |
          (prependToAll(w, x::xs) ++ (appendToAll(l1, x) ++ concatLists(l1,xs))).content               ==| trivial |
          (prependToAll(w, x::xs) ++ concatLists(l1,x::xs)).content
        }.qed
      }
    }
  }.holds

  //Generalizing the previous theorem
  def clLeftDistributiveAppend[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    decreases(l1.size)
    concatLists(l1 ++ l2, l3).content == (concatLists(l1,l3) ++ concatLists(l2,l3)).content because {
      l1 match {
        case Nil() => true
        case x :: xs => {
          check {concatLists((x::xs) ++ l2, l3).content == concatLists(x:: (xs ++ l2), l3).content} &&
          check {concatLists(x:: (xs ++ l2), l3).content == (prependToAll(x, l3) ++ concatLists(xs ++ l2,l3)).content because {clInductLeft(x,xs++l2,l3)}} &&
          check {(prependToAll(x, l3) ++ concatLists(xs ++ l2,l3)).content == (prependToAll(x, l3) ++ (concatLists(xs ,l3) ++ concatLists(l2,l3))).content because {check{xs.size < l1.size} && clLeftDistributiveAppend(xs,l2,l3)}} &&
          check {(prependToAll(x, l3) ++ (concatLists(xs ,l3) ++ concatLists(l2,l3))).content == ((prependToAll(x, l3) ++ concatLists(xs ,l3)) ++ concatLists(l2,l3)).content because{ListSpecs.appendAssoc(prependToAll(x, l3), concatLists(xs ,l3), concatLists(l2,l3))}} &&
          check {((prependToAll(x, l3) ++ concatLists(xs ,l3)) ++ concatLists(l2,l3)).content == (concatLists(x::xs ,l3) ++ concatLists(l2,l3)).content because {clInductLeft(x,xs,l3)}}
        }
      }
    }
  }.holds

  def clRightDistributiveAppend[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    concatLists(l1, l2++l3).content == (concatLists(l1, l2) ++ concatLists(l1,l3)).content because {
      l2 match {
        case Nil() => true
        case x :: xs =>  {
          check {concatLists(l1, (x::xs)++l3).content == ((appendToAll(l1, x).content) ++ (concatLists(l1, (xs++l3))).content)}
          check {((concatLists(l1, (xs++l3))).content) == (concatLists(l1, xs) ++ concatLists(l1,l3)).content because {clRightDistributiveAppend(l1,xs,l3)}}
          check {((appendToAll(l1, x).content) ++ (concatLists(l1, (xs++l3))).content) == ((appendToAll(l1, x).content) ++ (concatLists(l1, xs) ++ concatLists(l1,l3)).content) because {clRightDistributiveAppend(l1,xs,l3)}} &&
          check {((appendToAll(l1, x).content) ++ (concatLists(l1, xs) ++ concatLists(l1,l3)).content) == (concatLists(l1, x::xs) ++ concatLists(l1,l3)).content}
        }
      }
    }
  }.holds

  // reversing the combination of reverses results the combination
  // pretty nice theorem, it's a shame I currently don't use it
  def doubleReverseConcatList[T](l1: List[List[T]], l2: List[List[T]]): Boolean = {
    decreases(l1.size)
    concatLists(l1,l2).content == reverseAll(concatLists(reverseAll(l2), reverseAll(l1))).content because {
      l1 match {
        case Nil() => check {concatLists(Nil[List[T]](), l2).content == reverseAll(concatLists(reverseAll(l2), reverseAll(l1))).content}
        case x :: xs => {
          concatLists(x :: xs,l2).content                                                                                        ==| clInductLeft(x,xs,l2) |
          (prependToAll(x,l2) ++ concatLists(xs, l2)).content                                                                    ==| convertPaToAa(x,l2) |
          (reverseAll(appendToAll(reverseAll(l2),x.reverse)) ++ concatLists(xs, l2)).content                                     ==| doubleReverseConcatList(xs,l2) |
          (reverseAll(appendToAll(reverseAll(l2),x.reverse)) ++ reverseAll(concatLists(reverseAll(l2),reverseAll(xs)))).content  ==| reverseAllConcat(appendToAll(reverseAll(l2),x.reverse),concatLists(reverseAll(l2),reverseAll(xs))) |
          reverseAll(appendToAll(reverseAll(l2),x.reverse) ++ concatLists(reverseAll(l2),reverseAll(xs))).content                ==| trivial |
          reverseAll(concatLists(reverseAll(l2),x.reverse :: reverseAll(xs))).content                                            ==| trivial |
          reverseAll(concatLists(reverseAll(l2),reverseAll(x::xs))).content
        }.qed
      }
    }
  }.holds

  //apply structural induction on both left and right hand side operators
  def explode[T](x: List[T], xs: List[List[T]], y: List[T], ys: List[List[T]]): Boolean = {
    concatLists(x::xs, y::ys).content == (List(x ++ y) ++ appendToAll(xs,y) ++ prependToAll(x,ys) ++ concatLists(xs, ys)).content because {
        concatLists(x::xs, y::ys).content                                                              ==| trivial                                                                                               |
        (appendToAll(x::xs, y) ++ concatLists(x::xs, ys)).content                                      ==| clInductLeft(x,xs,ys)                                                                  |
        (appendToAll(x::xs, y) ++ (prependToAll(x, ys) ++ concatLists(xs, ys))).content                ==| (appendToAll(x::xs, y) == ((x ++ y) :: appendToAll(xs, y)))                                           |
        (((x ++ y) :: appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ concatLists(xs, ys))).content     ==| ((x ++ y) :: appendToAll(xs, y) == (List(x ++ y) ++ appendToAll(xs, y)))                              |
        ((List(x ++ y) ++ appendToAll(xs, y)) ++ (prependToAll(x, ys) ++ concatLists(xs, ys))).content ==| ListSpecs.appendAssoc(List(x ++ y) ++ appendToAll(xs, y), prependToAll(x, ys), concatLists(xs, ys))  |
        (((List(x ++ y) ++ appendToAll(xs, y)) ++ prependToAll(x, ys)) ++ concatLists(xs, ys)).content
    }.qed
  }.holds

  // If the content of two lists is the same, than combining them to the same
  // list will yield lists with the same content
  //TODO the theorem has a pair with the second arguments, but it will involve the sort-of dual of every other theorems
  def clContentEquals[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    require(l1.content == l2.content)
    concatLists(l1, l3).content == concatLists(l2, l3).content because {
      l3 match {
        case Nil() => check{true}
        case x::xs => {
          check {concatLists(l1, x::xs).content == (appendToAll(l1, x) ++ concatLists(l1, xs)).content because {clInductRight(l1,x,xs)}} &&
          check {(appendToAll(l1, x) ++ concatLists(l1, xs)).content == (appendToAll(l1, x).content ++ concatLists(l1, xs).content)} &&
          check {(appendToAll(l1, x).content ++ concatLists(l1, xs).content) == (appendToAll(l1, x).content ++ concatLists(l2, xs).content) because {clContentEquals(l1,l2,xs)}} &&
          check {(appendToAll(l1, x).content ++ concatLists(l2, xs).content) == (appendToAll(l2, x).content ++ concatLists(l2, xs).content) because {aaWithContentEquals(l1,l2,x)}} &&
          check {(appendToAll(l2, x).content ++ concatLists(l2, xs).content) == (appendToAll(l2, x) ++ concatLists(l2, xs)).content} &&
          check {(appendToAll(l2, x) ++ concatLists(l2, xs)).content == (concatLists(l2, x::xs)).content because {clInductRight(l2,x,xs)}}
        }
      }
    }
  }.holds

  def clContentEquals2[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    require(l2.content == l3.content)
    check {reverseAll(l2).content == reverseAll(l3).content because{reverseContentEquals(l2,l3)}}
    concatLists(l1,l2).content == concatLists(l1,l3).content because {
      check {concatLists(l1,l2).content == reverseAll(concatLists(reverseAll(l2),reverseAll(l1))).content because {doubleReverseConcatList(l1,l2)}} &&
      check {reverseAll(concatLists(reverseAll(l2),reverseAll(l1))).content == reverseAll(concatLists(reverseAll(l3),reverseAll(l1))).content because {check {reverseAll(l2).content == reverseAll(l3).content because{reverseContentEquals(l2,l3)}} && replaceUnderReverseAll(reverseAll(l2), reverseAll(l3), reverseAll(l1))}} &&
      check {reverseAll(concatLists(reverseAll(l3),reverseAll(l1))).content == concatLists(l1,l3).content because {doubleReverseConcatList(l1,l3)}}
    }
  }.holds

  //prepending the suffix can be moved outside the list combination
  def replaceConcatPrepend[T](prefix: List[T], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    concatLists(prependToAll(prefix,l2),l3).content == prependToAll(prefix, concatLists(l2,l3)).content because {
      l3 match {
        case Nil() => true
        case x :: xs => {
          check {concatLists(prependToAll(prefix,l2),x::xs).content == (appendToAll(prependToAll(prefix, l2), x) ++ concatLists(prependToAll(prefix,l2),xs)).content because {clInductRight(prependToAll(prefix, l2), x, xs)}} &&
          check {(appendToAll(prependToAll(prefix, l2), x) ++ concatLists(prependToAll(prefix,l2),xs)).content == (appendToAll(prependToAll(prefix, l2), x) ++ prependToAll(prefix, concatLists(l2,xs))).content because {replaceConcatPrepend(prefix, l2, xs)}} &&
          check {(appendToAll(prependToAll(prefix, l2), x) ++ prependToAll(prefix, concatLists(l2,xs))).content == (prependToAll(prefix, appendToAll(l2, x)) ++ prependToAll(prefix, concatLists(l2,xs))).content because {appendPrependOrder(prefix, l2,x)}} &&
          check {(prependToAll(prefix, appendToAll(l2, x)) ++ prependToAll(prefix, concatLists(l2,xs))).content == prependToAll(prefix, appendToAll(l2, x) ++ concatLists(l2,xs)).content because {paDistributiveOverAppend(prefix, appendToAll(l2, x), concatLists(l2,xs))}} &&
          check {prependToAll(prefix, appendToAll(l2, x) ++ concatLists(l2,xs)).content == prependToAll(prefix, concatLists(l2,x::xs)).content because {clInductRight(l2,x,xs)}}
        }
      }
    }
  }.holds


  def replaceUnderReverseAll[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    require(l1.content == l2.content)
    reverseAll(concatLists(l1,l3)).content == reverseAll(concatLists(l2,l3)).content because {
        check {concatLists(l1,l3).content == concatLists(l2,l3).content because {clContentEquals(l1,l2,l3)}} &&
        reverseContentEquals(concatLists(l1,l3), concatLists(l2,l3))
    }
  }.holds

  //What the hell takes 150s on this postcondition to verify???
  def clAssociative[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]]): Boolean = {
    concatLists(concatLists(l1,l2),l3).content == concatLists(l1, concatLists(l2,l3)).content because {
      l1 match {
        case Nil() => check {concatLists(concatLists(Nil[List[T]](),l2),l3).content == concatLists(Nil[List[T]](), concatLists(l2,l3)).content}
        case x :: xs => {
          concatLists(concatLists(x::xs,l2),l3).content ==|  (clInductLeft(x,xs,l2) && clContentEquals(concatLists(x::xs,l2),prependToAll(x,l2) ++ concatLists(xs,l2) , l3)) |
          concatLists(prependToAll(x,l2) ++ concatLists(xs,l2),l3).content ==| clLeftDistributiveAppend(prependToAll(x,l2), concatLists(xs,l2) ,l3) |
          (concatLists(prependToAll(x,l2),l3) ++ concatLists(concatLists(xs,l2),l3)).content ==| clAssociative(xs,l2,l3) |
          (concatLists(prependToAll(x,l2),l3) ++ concatLists(xs, concatLists(l2,l3))).content ==| replaceConcatPrepend(x,l2,l3) |
          (prependToAll(x,concatLists(l2,l3)) ++ concatLists(xs, concatLists(l2,l3))).content ==| clInductLeft(x,xs,concatLists(l2,l3)) |
          concatLists(x::xs, concatLists(l2,l3)).content
        }.qed
      }
    }
  }.holds

  //experiment
  @library
  def generalRemoveAndAdd[T](l:List[List[T]], x: List[T], f: List[List[T]] => List[List[T]], i: List[T] => List[T]): Boolean = {
    require(forall((z: List[T], zs: List[List[T]]) => f(z::zs).content == (i(z)::f(zs)).content ))
    require(l.contains(x))
    f(l).content == (i(x) :: f(l-x)).content because {
      l match {
        case Nil() => false
        case y::ys if ((x == y) && (ys contains x)) => {
          check {f(x::ys).content == (i(x) :: f(ys)).content} &&
          check {(i(x) ::f(ys)).content == (Set(i(x)) ++ f(ys).content)} &&
          check {(Set(i(x)) ++ f(ys).content) == (Set(i(x)) ++ (i(x) :: f(ys-x)).content) because {check{ys.contains(x)} && check{forall((z: List[T], zs: List[List[T]]) => f(z::zs).content == (i(z)::f(zs)).content )} && generalRemoveAndAdd(ys,x,f,i)}} &&
          check {(Set(i(x)) ++ (i(x) :: f(ys-x)).content) == (i(x) :: (i(x)::f(ys-x))).content} &&
          check {(i(x) :: (i(x)::f(ys-x))).content == (i(x)::f(ys-x)).content} &&
          check {(i(x)::f(ys-x)).content == (i(x)::f((x::ys)-x)).content}
        }
        case y::ys if (x==y) => {
          check {f(x::ys).content == (i(x) ::f(ys)).content} &&
          check {!ys.contains(x)}
          check {ys == ((x::ys)-x) because {prependAndRemoveNotContaining(x,ys)}} &&
          check {(i(x) ::f(ys)).content == (i(x) ::f((x::ys)-x)).content}
        }
        case y::ys => {
          check {f(y::ys).content == (i(y) :: f(ys)).content} &&
          check {(i(y) :: f(ys)).content == (Set(i(y)) ++f(ys).content)} &&
          check {(Set(i(y)) ++f(ys).content) == (Set(i(y)) ++(i(x) :: f(ys-x)).content) because {check{ys.contains(x)} && check{forall((z: List[T], zs: List[List[T]]) => f(z::zs).content == (i(z)::f(zs)).content )} && generalRemoveAndAdd(ys,x,f,i)}} &&
          check {(Set(i(y)) ++(i(x) :: f(ys-x)).content) == (Set(i(y)) ++ Set(i(x)) ++ f(ys-x).content)} &&
          check {(Set(i(y)) ++ Set(i(x)) ++ f(ys-x).content) == (Set(i(x)) ++ (Set(i(y)) ++ f(ys-x).content))} &&
          check {(Set(i(x)) ++ (Set(i(y)) ++ f(ys-x).content)) == (Set(i(x)) ++ (i(y) :: f(ys-x)).content)} &&
          check {(Set(i(x)) ++ (i(y) :: f(ys-x)).content) == (Set(i(x)) ++ f(y::(ys-x)).content)} &&
          check {(Set(i(x)) ++ f(y::(ys-x)).content) == (Set(i(x)) ++ f((y::ys)-x).content)}
        }
      }
    }
  }.holds

}
