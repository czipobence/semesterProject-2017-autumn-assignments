import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

case class Lang[T](list: List[List[T]]) {
    /*def appendToAllSplit(suffix: List[T], l: List[List[T]]): Boolean = {
      l match {
        case Nil() => true
        case x :: xs => appendToAll(l, suffix) == (x ++ suffix) :: appendToAll(xs, suffix)
      }
    }.holds

  def appendToAllLemma(suffix: List[T], prefix: List[T], list: List[List[T]]): Boolean = {
    require(list.contains(prefix))
    appendToAll(list, suffix).contains(prefix ++ suffix)
  }.holds

  def appendToAllLemma2(suffix: List[T], prefix: List[T], list: List[List[T]]): Boolean = {
    require(list.contains(prefix))
    appendToAll(list, suffix).contains(prefix ++ suffix) because {
      list match {
        case Nil() => check {appendToAll(list, suffix).contains(prefix ++ suffix)}
        case Cons(prefix, _) => check {appendToAll(list, suffix).contains(prefix ++ suffix)}
        case Cons(x,xs) => {
          appendToAll(Cons(x, xs), suffix).contains(prefix ++ suffix)                                 ==| appendToAllSplit(suffix, list)  |
          ((x ++ suffix) :: appendToAll(xs, suffix)).contains(prefix ++ suffix)                       ==| trivial                         |
          ((x ++ suffix) == (prefix ++ suffix) || appendToAll(xs, suffix).contains(prefix ++ suffix)) ==| trivial                         |
          appendToAll(xs, suffix).contains(prefix ++ suffix)                                          ==| trivial                         |
          appendToAllLemma2(suffix, prefix, xs)
        }
      }
    }.qed
  }.holds*/

  def combine(that: Lang[T]): Lang[T] = {
    Lang[T](Lang.combineLists(this.list, that.list))
  }.ensuring {res =>
    this.list.forall(l1 => that.list.forall(l2 => res.contains(l1 ++ l2)))
  }

  def ::(t: List[T]): Lang[T] = {
    Lang[T](t :: this.list)
  } ensuring { res =>
    (res.list.content == this.list.content + t) &&
    (res.list.size == this.list.size + 1)
  }

  def ++(that: Lang[T]): Lang[T] = (
    Lang[T](this.list ++ that.list)
  ) ensuring { res =>
      (res.list.content == this.list.content ++ that.list.content) &&
      (res.list.size == this.list.size + that.list.size) &&
      (that.list != Nil[List[T]]() || res.list == this.list)
    }

  def == (that: Lang[T]): Boolean = {
    this.list.content == that.list.content
  }

  def contains(word: List[T]): Boolean = list.contains(word)
}

object Lang {
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

import Lang._

object LangSpecs {
  def prependToAllLemmaMap[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAllMap(prefix,l) == appendToAll(l.map(lst => lst.reverse) , prefix.reverse).map(lst => lst.reverse)
  }.holds

  def prependToAllLemma[T](prefix: List[T], l: List[List[T]]): Boolean = {
    prependToAll(prefix,l) == reverseAll(appendToAll(reverseAll(l) , prefix.reverse))
  }.holds


  //the equals operator is symmectric, which means that if a == b than b==a
  def equalsAssoc[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 == l2) == (l2 == l1)
  }.holds

  //It should verify by definition
  // todo move lemmas to static object
  def combinationLemma[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 combine l2) == Lang[T](combineLists(l1.list, l2.list))
  }.holds

  def reverseCombinationLemma[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    Lang[T](combineLists(l1.list, l2.list)) == (l1 combine l2) because {
      combinationLemma(l1,l2) && equalsAssoc((l1 combine l2), Lang[T](combineLists(l1.list, l2.list)))
    }
  }.holds

  def unitLang[T](): Lang[T] = Lang[T](List(Nil()))

  def nullLang[T](): Lang[T] = Lang[T](Nil())

  def rightUnitCombine[T](l1: Lang[T]): Boolean = {

    l1.combine(unitLang()) == l1 because {
      l1 match {
        case Lang(Nil()) => check {l1.combine(unitLang()) == l1}
        case Lang(x :: xs) => {
          Lang[T](x :: xs).combine(unitLang())                                          ==| trivial                                             |
          (x:: Lang[T](xs)).combine(unitLang())                                         ==| combineDistributiveLeft(x, Lang[T](xs), unitLang()) |
          Lang[T](prependToAll(x, unitLang().list)) ++ (Lang[T](xs) combine unitLang()) ==| prependToUnitLang(x)                                |
          Lang[T](List(x)) ++ (Lang[T](xs) combine unitLang())                          ==| rightUnitCombine(Lang[T](xs))                       |
          Lang[T](List(x)) ++ Lang[T](xs)                                               ==| trivial                                             |
          Lang[T](List(x) ++ xs)                                                        ==| trivial                                             |
          Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def prependToUnitLang[T](prefix: List[T]): Boolean = {
    prependToAll(prefix, unitLang().list) == List(prefix) because {
      prependToAll(prefix, unitLang().list)                                                                 ==| trivial |
      prependToAll(prefix, List[List[T]](Nil[T]()))                                                         ==| prependToAllLemma(prefix, List[List[T]](Nil[T]())) |
      reverseAll(appendToAll(reverseAll(List[List[T]](Nil[T]())), prefix.reverse))                          ==| trivial |
      reverseAll(appendToAll(List[List[T]](Nil[T]()),prefix.reverse))                                       ==| trivial |
      reverseAll(List(prefix.reverse))                                                                      ==| trivial |
      List(prefix.reverse.reverse)                                                                          ==| ListSpecs.reverseReverse(prefix) |
      List(prefix)
    }.qed
  }.holds

  //reverseAll for SingleList, actually trivial
  def reverseAllSingleItem[T](list: List[T]): Boolean = {
    reverseAll(List(list)) == List(list.reverse)
  }.holds

  def leftUnitCombine[T](l1: Lang[T]): Boolean = {
    unitLang().combine(l1) == l1 because {
      l1 match {
        case Lang(Nil()) => check {unitLang().combine(l1) == l1}
        case Lang(x :: xs) => {
          (unitLang().combine(x ::Lang[T](xs)))                                           ==| combineDistributiveRight(unitLang(), x, Lang[T](xs))  |
          (Lang[T](appendToAll(unitLang().list, x)) ++ (unitLang() combine  Lang[T](xs))) ==| trivial                                             |
          (Lang[T](List(x)) ++ (unitLang() combine  Lang[T](xs)))                         ==| leftUnitCombine(Lang[T](xs))                        |
          (Lang[T](List(x)) ++  Lang[T](xs))                                              ==| trivial                                             |
          Lang[T](List(x) ++ xs)                                                          ==| trivial                                             |
          Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def rightNullCombine[T](l1: Lang[T]): Boolean = {
    l1.combine(nullLang[T]()) == nullLang[T]()
  }.holds

  def leftNullCombine[T](l1: Lang[T]): Boolean = {
    nullLang[T]().combine(l1) == nullLang[T]()
  }.holds

  def associativity[T](l1: Lang[T], l2: Lang[T], l3:Lang[T]): Boolean = {
    (l1 combine (l2 combine l3)) == ((l1 combine l2) combine l3)
  }.holds

  def combineDistributiveRight[T](l1: Lang[T], w: List[T], l2: Lang[T]): Boolean = {
    ((l1 combine (w :: l2)) == (Lang[T](appendToAll(l1.list, w)) ++ (l1 combine l2))) because {
      (l1 combine (w :: l2))                                                      ==| combinationLemma(l1, w::l2) |
      Lang[T](combineLists(l1.list, (w :: l2).list))                              ==| trivial |
      Lang[T](combineLists(l1.list, w :: l2.list))                                ==| trivial |
      Lang[T](appendToAll(l1.list, w) ++ combineLists(l1.list, l2.list))          ==| trivial |
      Lang[T](appendToAll(l1.list, w)) ++ Lang[T](combineLists(l1.list, l2.list)) ==| reverseCombinationLemma(l1, l2) |
      Lang[T](appendToAll(l1.list, w)) ++ (l1 combine l2)
    }.qed
  }.holds

  def combineDistributiveLeft[T](w: List[T], l1: Lang[T], l2: Lang[T]): Boolean = {
    ( (w ::  l1) combine l2) == Lang[T](prependToAll(w, l2.list)) ++ (l1 combine l2)
  }.holds
}
