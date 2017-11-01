import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

//to split into multiple files just incude them and pass all to stainless
import ListOfLists._
import ListOfListsSpecs._

case class Lang[T](list: List[List[T]]) {

  def combine(that: Lang[T]): Lang[T] = {
    Lang[T](combineLists(this.list, that.list))
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

  def sameAs(that: Lang[T]): Boolean = {
    this.list.content == that.list.content
  }

  def contains(word: List[T]): Boolean = list.contains(word)
}

object LangSpecs {


  //the equals operator is symmectric, which means that if a == b than b==a
  def equalsAssoc[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 == l2) == (l2 == l1)
  }.holds

  //It should verify by definition
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
    ( (w ::  l1) combine l2) == Lang[T](prependToAll(w, l2.list)) ++ (l1 combine l2) because {
      ((w ::  l1) combine l2)                                                           ==| trivial                                           |
      Lang[T](combineLists((w ::  l1).list, l2.list))                                   ==| trivial                                           |
      Lang[T](combineLists((w ::  l1.list), l2.list))                                   ==| combineDistributiveLeftHelper(w,l1.list,l2.list)  |
      Lang[T](prependToAll(w, l2.list) ++ combineLists(l1.list, l2.list))               ==| trivial                                           |
      Lang[T](prependToAll(w, l2.list)) ++ Lang[T](combineLists(l1.list, l2.list))      ==| trivial                                           |
      Lang[T](prependToAll(w, l2.list)) ++ (l1 combine l2)
    }.qed
  }.holds
}
