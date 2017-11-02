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

object Lang {
  def unitLang[T](): Lang[T] = Lang[T](List(Nil()))
  def nullLang[T](): Lang[T] = Lang[T](Nil())
}

import Lang._

object LangSpecs {

  def rightUnitCombine[T](l1: Lang[T]): Boolean = {

    l1.combine(unitLang()) sameAs l1 because {
      l1 match {
        case Lang(Nil()) => true
        case Lang(x :: xs) => {
          Lang[T](x :: xs).combine(unitLang())                                          ==| trivial                                             |
          (x:: Lang[T](xs)).combine(unitLang())                                         ==| combineDistributiveLeft(x, Lang[T](xs), unitLang()) |
          Lang[T](prependToAll(x, unitLang().list)) ++ (Lang[T](xs) combine unitLang()) ==| prependToEmptyList(x)                               |
          Lang[T](List(x)) ++ (Lang[T](xs) combine unitLang())                          ==| rightUnitCombine(Lang[T](xs))                       |
          Lang[T](List(x)) ++ Lang[T](xs)                                               ==| trivial                                             |
          Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def leftUnitCombine[T](l1: Lang[T]): Boolean = {
    unitLang().combine(l1) sameAs l1 because {
      l1 match {
        case Lang(Nil()) => true
        case Lang(x :: xs) => {
          (unitLang().combine(x ::Lang[T](xs)))                                           ==| combineDistributiveRight(unitLang(), x, Lang[T](xs))  |
          (Lang[T](appendToAll(unitLang().list, x)) ++ (unitLang() combine  Lang[T](xs))) ==| trivial                                             |
          (Lang[T](List(x)) ++ (unitLang() combine  Lang[T](xs)))                         ==| leftUnitCombine(Lang[T](xs))                        |
          (Lang[T](List(x)) ++  Lang[T](xs))                                              ==| trivial                                             |
          Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def rightNullCombine[T](l1: Lang[T]): Boolean = {
    l1.combine(nullLang[T]()) sameAs nullLang[T]()
  }.holds

  def leftNullCombine[T](l1: Lang[T]): Boolean = {
    nullLang[T]().combine(l1) sameAs nullLang[T]()
  }.holds

  def associativity[T](l1: Lang[T], l2: Lang[T], l3:Lang[T]): Boolean = {
    (l1 combine (l2 combine l3)) sameAs ((l1 combine l2) combine l3)
  }.holds

  def combineDistributiveRight[T](l1: Lang[T], w: List[T], l2: Lang[T]): Boolean = {
    ((l1 combine (w :: l2)) sameAs (Lang[T](appendToAll(l1.list, w)) ++ (l1 combine l2)))
  }.holds

  def combineDistributiveLeft[T](w: List[T], l1: Lang[T], l2: Lang[T]): Boolean = {
    ( (w ::  l1) combine l2) sameAs Lang[T](prependToAll(w, l2.list)) ++ (l1 combine l2) because {
        combineListDistributiveLeft(w,l1.list,l2.list)
    }
  }.holds

  def listContentEquals[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 == l2) ==> (l1.content == l2.content)
  }.holds

  def equalityIsSame[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 == l2) ==> (l1 sameAs l2)
  }.holds
}
