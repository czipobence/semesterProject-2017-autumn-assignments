import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

//to split into multiple files just incude them and pass all to stainless
import ListOfLists._
import AppendPrependSpecs._
import ConcatListsSpecs._

case class Lang[T](list: List[List[T]]) {

  def concat(that: Lang[T]): Lang[T] = {
    Lang[T](concatLists(this.list, that.list))
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

  def --(that: Lang[T]): Lang[T] = {
    Lang[T](this.list -- that.list)
  } ensuring { res =>
    (res.list.size <= this.list.size) &&
    (res.list.content == this.list.content -- that.list.content )
  }

  def == (that: Lang[T]): Boolean = {
    this.list.content == that.list.content
  }

  def sameAs(that: Lang[T]): Boolean = {
    this.list.content == that.list.content
  }

  def subsetOf(that: Lang[T]): Boolean = {
    this.list.content subsetOf that.list.content
  }.ensuring{res => res ==> forall((item: List[T]) => this.list.contains(item) ==> that.list.contains(item)  ) }

  def contains(word: List[T]): Boolean = list.contains(word)

  /*def power (i: Int): Lang[T] = {
    require(i >= BigInt(0))
    decreases(i)
    i match {
      case 0 => Lang[T](List(Nil()))
      case _ => this concat (this power (i-1))
    }
  }*/

  def ^ (i: BigInt): Lang[T] = {
    require(i >= BigInt(0))
    decreases(i)
    i match {
      case BigInt(0) => Lang[T](List(Nil()))
      case _ => this concat (this ^ (i-1))
    }
  }

  def close(i: BigInt): Lang[T] = {
    require(i >= BigInt(0))
    decreases(i)
    i match {
      case BigInt(0) => this ^ i
      case _ => (this close (i-1)) ++ (this ^ i)
    }
  }

  def :^ (i: BigInt): Lang[T] = {
    require(i >= BigInt(0))
    decreases(i)
    i match {
      case BigInt(0) => Lang[T](List(Nil()))
      case _ =>  (this ^ (i-1)) concat this
    }
  }

}

object Lang {
  def unitLang[T](): Lang[T] = Lang[T](List(Nil()))
  def nullLang[T](): Lang[T] = Lang[T](Nil())
}

import Lang._

object LangSpecs {

  def rightUnitConcat[T](l1: Lang[T]): Boolean = {

    l1.concat(unitLang()) sameAs l1 because {
      l1 match {
        case Lang(Nil()) => true
        case Lang(x :: xs) => {
          Lang[T](x :: xs).concat(unitLang())                                          ==| trivial                                             |
          (x:: Lang[T](xs)).concat(unitLang())                                         ==| concatDistributiveLeft(x, Lang[T](xs), unitLang()) |
          Lang[T](prependToAll(x, unitLang().list)) ++ (Lang[T](xs) concat unitLang()) ==| prependToEmptyList(x)                               |
          Lang[T](List(x)) ++ (Lang[T](xs) concat unitLang())                          ==| rightUnitConcat(Lang[T](xs))                       |
          Lang[T](List(x)) ++ Lang[T](xs)                                               ==| trivial                                             |
          Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def leftUnitConcat[T](l1: Lang[T]): Boolean = {
    unitLang().concat(l1) sameAs l1 because {
      l1 match {
        case Lang(Nil()) => true
        case Lang(x :: xs) => {
          (unitLang().concat(x ::Lang[T](xs)))                                           ==| concatDistributiveRight(unitLang(), x, Lang[T](xs))  |
          (Lang[T](appendToAll(unitLang().list, x)) ++ (unitLang() concat  Lang[T](xs))) ==| trivial                                             |
          (Lang[T](List(x)) ++ (unitLang() concat  Lang[T](xs)))                         ==| leftUnitConcat(Lang[T](xs))                        |
          (Lang[T](List(x)) ++  Lang[T](xs))                                              ==| trivial                                             |
          Lang[T](x :: xs)
        }.qed
      }
    }
  }.holds

  def rightNullConcat[T](l1: Lang[T]): Boolean = {
    l1.concat(nullLang[T]()) sameAs nullLang[T]()
  }.holds

  def leftNullConcat[T](l1: Lang[T]): Boolean = {
    nullLang[T]().concat(l1) sameAs nullLang[T]()
  }.holds

  def associativity[T](l1: Lang[T], l2: Lang[T], l3:Lang[T]): Boolean = {
    (l1 concat (l2 concat l3)) sameAs ((l1 concat l2) concat l3) because {
      clAssociative(l1.list, l2.list, l3.list)
    }
  }.holds

  def concatDistributiveRight[T](l1: Lang[T], w: List[T], l2: Lang[T]): Boolean = {
    ((l1 concat (w :: l2)) sameAs (Lang[T](appendToAll(l1.list, w)) ++ (l1 concat l2)))
  }.holds

  def concatDistributiveLeft[T](w: List[T], l1: Lang[T], l2: Lang[T]): Boolean = {
    ( (w ::  l1) concat l2) sameAs Lang[T](prependToAll(w, l2.list)) ++ (l1 concat l2) because {
        clInductLeft(w,l1.list,l2.list)
    }
  }.holds

  def concatDistributiveAppendLeft[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    ((l1 ++ l2) concat l3) sameAs ((l1 concat l3) ++ (l2 concat l3)) because {
      clLeftDistributiveAppend(l1.list,l2.list,l3.list)
    }
  }.holds

  def concatSameAs[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    require(l1 sameAs l2)
    (l1 concat l3) sameAs (l2 concat l3) because {
      clContentEquals(l1.list,l2.list,l3.list)
    }
  }.holds

  def concatSameAs2[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    require(l2 sameAs l3)
    (l1 concat l2) sameAs (l1 concat l3) because {
      clContentEquals2(l1.list,l2.list,l3.list)
    }
  }.holds

  def couldHaveDefinedOtherWay[T](l: Lang[T], i: BigInt): Boolean = {
    require(i >= BigInt(0))
    decreases(i)
    (l ^ i) sameAs (l :^i) because {
      i match {
        case BigInt(0) => check{(l^0) sameAs (l:^0)}
        case BigInt(1) => {
          check {(l^1) sameAs (l concat (l^0))} &&
          check {(l concat (l^0)) sameAs (l concat unitLang[T]())} &&
          check {(l concat unitLang[T]()) sameAs l because {rightUnitConcat(l)}} &&
          check {l sameAs (unitLang[T]() concat l) because {leftUnitConcat(l)}} &&
          check {(unitLang[T]() concat l) sameAs ((l:^0) concat l)} &&
          check {((l:^0) concat l) sameAs l^1}
        }
        case _ => {
          check {(l^i) sameAs (l concat (l ^ (i-1)))} &&
          check {(l concat (l ^ (i-1))) sameAs (l concat (l :^ (i-1))) because{couldHaveDefinedOtherWay(l,i-1) && concatSameAs2(l, (l ^ (i-1)), (l :^ (i-1)))}} &&
          check {(l concat (l :^ (i-1))) sameAs (l concat ((l :^ (i-2)) concat l)) because {concatSameAs2(l, (l :^ (i-1)), ((l :^ (i-2)) concat l))}} &&
          check {(l concat ((l :^ (i-2)) concat l)) sameAs ((l concat (l :^ (i-2))) concat l) because {associativity(l, l:^(i-2),l)}} &&
          check {((l concat (l :^ (i-2))) concat l) sameAs ((l concat (l ^ (i-2))) concat l) because {couldHaveDefinedOtherWay(l,i-2) && concatSameAs2(l, (l :^ (i-2)), (l ^ (i-2))) && concatSameAs((l concat (l :^ (i-2))), (l concat (l ^ (i-2))), l)}} &&
          check {((l concat (l ^ (i-2))) concat l) sameAs ((l ^ (i-1)) concat l)} &&
          check {((l ^ (i-1)) concat l) sameAs ((l :^ (i-1)) concat l) because{couldHaveDefinedOtherWay(l,i-1)} && concatSameAs((l ^ (i-1)), (l :^ (i-1)), l)} &&
          check {((l :^ (i-1)) concat l) sameAs (l :^ i)}
        }
      }
    }
  }.holds

  def nullLangClose[T](n: BigInt): Boolean = {
    require(n >= BigInt(0))
    (nullLang() close n) sameAs unitLang() because {
      n match {
        case BigInt(0) => check{(nullLang() close 0) == unitLang()}
        case _ => {
          check {(nullLang() close n) == (nullLang() close (n-1)) ++ (nullLang() ^ n)} &&
          check {(nullLang() close (n-1)) ++ (nullLang() ^ n) == unitLang() ++ (nullLang() ^ n) because{nullLangClose(n-1)}} &&
          check {unitLang() ++ (nullLang() ^ n) == unitLang() ++ nullLang()} &&
          check {unitLang() ++ nullLang() == unitLang()}
        }
      }
    }
  }.holds

  def unitLangPow[T](n: BigInt): Boolean = {
    require(n >= BigInt(0))
    (unitLang() ^ n) sameAs unitLang() because {
      n match {
        case BigInt(0) => true
        case _ => {
          check{(unitLang() ^ n) sameAs (unitLang() concat (unitLang() ^ (n-1)))} &&
          check{(unitLang() concat (unitLang() ^ (n-1))) sameAs (unitLang() concat unitLang() ^ n-1)} &&
          check{(unitLang() concat unitLang() ^ n-1) sameAs (unitLang ^ (n-1)) because{leftUnitConcat(unitLang ^ (n-1))}} &&
          check{(unitLang ^ (n-1)) sameAs (unitLang()) because {unitLangPow(n-1)}}
        }
      }
    }
  }.holds

  def unitLangClose[T](n: BigInt): Boolean = {
    require(n >= BigInt(0))
    (unitLang() close n) sameAs unitLang() because {
      n match {
        case BigInt(0) => check{(unitLang() close 0) sameAs unitLang()}
        case _ => {
          check {(unitLang() close n) sameAs (unitLang() close (n-1)) ++ (unitLang() ^ n)} &&
          check {(unitLang() close (n-1)) ++ (unitLang() ^ n) sameAs unitLang() ++ (unitLang() ^ n) because{unitLangClose(n-1)}} &&
          check {unitLang() ++ (unitLang() ^ n) sameAs unitLang() ++ unitLang() because{unitLangPow(n)}} &&
          check {unitLang() ++ unitLang() sameAs unitLang()}
        }
      }
    }
  }.holds

  def listContentEquals[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 == l2) ==> (l1.content == l2.content)
  }.holds

  def equalityIsSame[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 == l2) ==> (l1 sameAs l2)
  }.holds

  // Lemmas with subsetOf, stainless is able to verify the most of them,
  // they are just added for completeness
  def subsetOfTransitive[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    ((l1 subsetOf l2) && (l2 subsetOf l3)) ==> (l1 subsetOf l3)
  }.holds

  def inUnionSubset[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 subsetOf (l1 ++ l2)) && (l2 subsetOf (l1 ++ l2))
  }.holds

  def unionSubset[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    ((l1 subsetOf l3) && (l2 subsetOf l3)) ==> ((l1 ++ l2) subsetOf l3)
  }.holds

  def sameAsSubset[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 sameAs l2) ==> (l1 subsetOf l2)
  }.holds

  def sameAsSubsetTrans[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    ((l1 subsetOf l2) && (l2 sameAs l3)) ==> (l1 subsetOf l3)
  }.holds

  def subsetSplit[T](l1: Lang[T], l2: Lang[T]): Boolean = {
    (l1 subsetOf l2) ==> (l2 sameAs (l1 ++ (l2 -- l1)))
  }.holds

  def concatSubset[T](l1: Lang[T], l2: Lang[T], l3: Lang[T]): Boolean = {
    (l1 subsetOf l2) ==> ( (l1 concat l3) subsetOf (l2 concat l3) because {
      check {(l2 sameAs (l1 ++ (l2 -- l1)))} &&
      check {((l1 concat l3) subsetOf (l2 concat l3)) == ((l1 concat l3) subsetOf ((l1 ++ (l2 -- l1)) concat l3)) because {concatSameAs(l2,l1 ++ (l2 -- l1),l3)}} &&
      check {((l1 concat l3) subsetOf ((l1 ++ (l2 -- l1)) concat l3)) == ((l1 concat l3) subsetOf ((l1 concat l3) ++ ((l2 -- l1) concat l3))) because {concatDistributiveAppendLeft(l1, l2--l1, l3)}} &&
      check {((l1 concat l3) subsetOf ((l1 concat l3) ++ ((l2 -- l1) concat l3))) == true}
    })
  }.holds

}
