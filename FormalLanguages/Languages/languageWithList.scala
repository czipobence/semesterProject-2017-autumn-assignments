import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

case class Lang[T](list: List[List[T]]) {

  def appendToAll(suffix: List[T], l: List[List[T]]): List[List[T]] = {
    l match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => (x ++ suffix) :: appendToAll(suffix, xs)
    }
  }.ensuring {res: List[List[T]] => res.size == l.size &&
    !l.isEmpty ==> res.contains(l.head ++ suffix)/*res.forall(x => x.drop(x.size -suffix.size) == suffix )*/}

    def appendToAllSplit(suffix: List[T], l: List[List[T]]): Boolean = {
      l match {
        case Nil() => true
        case x :: xs => appendToAll(suffix, l) == (x ++ suffix) :: appendToAll(suffix, xs)
      }
    }.holds

  def appendToAllLemma(suffix: List[T], prefix: List[T], list: List[List[T]]): Boolean = {
    require(list.contains(prefix))
    appendToAll(suffix, list).contains(prefix ++ suffix)
  }.holds

  def appendToAllLemma2(suffix: List[T], prefix: List[T], list: List[List[T]]): Boolean = {
    require(list.contains(prefix))
    appendToAll(suffix, list).contains(prefix ++ suffix) because {
      list match {
        case Nil() => check {appendToAll(suffix, list).contains(prefix ++ suffix)}
        case Cons(prefix, _) => check {appendToAll(suffix, list).contains(prefix ++ suffix)}
        case Cons(x,xs) => {
          appendToAll(suffix, Cons(x, xs)).contains(prefix ++ suffix)                                 ==| appendToAllSplit(suffix, list)  |
          ((x ++ suffix) :: appendToAll(suffix, xs)).contains(prefix ++ suffix)                       ==| trivial                         |
          ((x ++ suffix) == (prefix ++ suffix) || appendToAll(suffix, xs).contains(prefix ++ suffix)) ==| trivial                         |
          appendToAll(suffix, xs).contains(prefix ++ suffix)                                          ==| trivial                         |
          appendToAllLemma2(suffix, prefix, xs)
        }
      }
    }.qed
  }.holds

  def createCombinedList(lst: List[List[T]]): List[List[T]] = {
    lst match {
      case Nil() => Nil[List[T]]()
      case Cons(x,xs) => appendToAll(x, this.list) ++ createCombinedList(xs)
    }
  }.ensuring {res: List[List[T]] => res.size == this.list.size * lst.size}

  /*def createCombinedListSizeLemma(lst: List[List[T]]):Boolean = {
    createCombinedList(lst).size == this.list.size * lst.size
  }.holds*/

  def combine(that: Lang[T]): Lang[T] = {
    Lang[T](createCombinedList(that.list))
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

  def unitLang (): Lang[T] = Lang[T](List(Nil()))

  def nullLang(): Lang[T] = Lang[T](Nil())

  def rightUnitCombine(l1: Lang[T]): Boolean = {
    l1.combine(unitLang()) == l1
  }.holds

  def leftUnitCombine(l1: Lang[T]): Boolean = {
    unitLang().combine(l1) == l1 because {
      l1 match {
        case Lang(Nil()) => check {unitLang().combine(l1) == l1}
        case Lang(x :: xs) => {
          check {(unitLang().combine(x ::Lang[T](xs))) == (Lang[T](appendToAll(x, unitLang().list)) ++ (unitLang() combine Lang[T](xs)))} && combineDistributive(x, unitLang, Lang[T](xs)) &&
          check {(Lang[T](appendToAll(x, unitLang().list)) ++ (unitLang() combine  Lang[T](xs))) == (Lang[T](List(x)) ++ (unitLang() combine  Lang[T](xs)))} &&
          check {(Lang[T](List(x)) ++ (unitLang() combine  Lang[T](xs))) == (Lang[T](List(x)) ++  Lang[T](xs))} && leftUnitCombine(Lang[T](xs)) &&
          check {(Lang[T](List(x)) ++  Lang[T](xs)) == (Lang[T](List(x) ++  xs))} &&
          check {Lang[T](List(x) ++ xs) == Lang[T](x :: xs) }
        }
      }
    }
  }.holds

  def leftUnitCombineFormatted(l1: Lang[T]): Boolean = {
    unitLang().combine(l1) == l1 because {
      l1 match {
        case Lang(Nil()) => check {unitLang().combine(l1) == l1}
        case Lang(x :: xs) => {
          (unitLang().combine(x ::Lang[T](xs))) == (Lang[T](appendToAll(x, unitLang().list)) ++ (unitLang() combine Lang[T](xs)))                     ==| combineDistributive(x, unitLang, Lang[T](xs))  |
          (Lang[T](appendToAll(x, unitLang().list)) ++ (unitLang() combine  Lang[T](xs))) == (Lang[T](List(x)) ++ (unitLang() combine  Lang[T](xs)))  ==| trivial                                        |
          (Lang[T](List(x)) ++ (unitLang() combine  Lang[T](xs))) == (Lang[T](List(x)) ++  Lang[T](xs))                                               ==| leftUnitCombine(Lang[T](xs))                   |
          (Lang[T](List(x)) ++  Lang[T](xs)) == (Lang[T](List(x) ++  xs))                                                                             ==| trivial                                        |
          Lang[T](List(x) ++ xs) == Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def rightNullCombine(l1: Lang[T]): Boolean = {
    l1.combine(nullLang()) == nullLang()
  }.holds

  def leftNullCombine(l1: Lang[T]): Boolean = {
    nullLang().combine(l1) == nullLang()
  }.holds

  def associativity(l1: Lang[T], l2: Lang[T], l3:Lang[T]): Boolean = {
    (l1 combine (l2 combine l3)) == ((l1 combine l2) combine l3)
  }.holds

  def combineDistributive(w: List[T], l1:Lang[T], l2: Lang[T]): Boolean = {
    (l1 combine (w :: l2)) == (Lang[T](appendToAll(w, l1.list)) ++ (l1 combine l2))
  }.holds
}
