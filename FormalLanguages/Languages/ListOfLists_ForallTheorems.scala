import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import ListOfLists._

object Existential {
  def exists[A](p: A => Boolean): Boolean = !forall((x: A) => !p(x))
  def exists[A, B](p: (A,B) => Boolean): Boolean = !forall((x: A,y: B) => !p(x,y))
}

import Existential._

object SetSpecs {
  def removeAndPrependContent[T](x: T, l: List[T]): Boolean = {
    (x:: (l-x)).content == (x::l).content because {
      check {(x:: (l-x)).content == Set(x) ++ (l-x).content} &&
      check {Set(x) ++ (l-x).content == Set(x) ++ (l.content -- Set(x))} &&
      check {Set(x) ++ (l.content -- Set(x)) == Set(x) ++ l.content} && //na apám ha ezt bebizonyítod, emelem kalapom
      check {Set(x) ++ l.content == (x::l).content}
    }
  }.holds

  def removeAndPrependFromContaining[T](x: T, l: List[T]): Boolean = {
    require (l.contains(x))
    l.content == (x:: (l-x)).content because {
      check {l.content == l.content ++ Set(x)} &&
      check {l.content ++ Set(x) == (x::l).content} &&
      check {(x::l).content == (x:: (l-x)).content because {removeAndPrependContent(x,l)}}
    }
  }.holds

  def contentEqualsBothContains[T](l1: List[T], l2: List[T]): Boolean = {
    require(l1.content == l2.content)
    forall((t: T) => l1.contains(t) == l2.contains(t))
  }.holds

  def theoremInsideForall2[T](x:T, xs:List[T], s2:List[T], t:T): Boolean = {
    require(s2.contains(x))
    ((xs-x).contains(t) == (s2-x).contains(t)) == ((x::xs).contains(t) == s2.contains(t)) because {
      if (t==x) {
        check {((xs-x).contains(x) == (s2-x).contains(x)) == ((x::xs).contains(x) == s2.contains(x))}
      } else {
        check {((xs-x).contains(t) == (s2-x).contains(t)) == ((x::(xs-x)).contains(t) == (x::(s2-x)).contains(t))} &&
        check {((x::(xs-x)).contains(t) == (x::(s2-x)).contains(t)) == ((x::(xs-x)).contains(t) == s2.contains(t)) because {removeAndPrependFromContaining(x,s2)}} &&
        check {((x::(xs-x)).contains(t) == s2.contains(t)) == ((x::xs).contains(t) == s2.contains(t)) because {removeAndPrependContent(x,xs)}}
      }

    }
  }.holds

  def theoremInsideForall[T](x: T, xs: List[T], s2: List[T]): Boolean = {
    require(s2.contains(x))
    forall((t: T) => ((xs-x).contains(t) == (s2-x).contains(t)) == ((x::xs).contains(t) == s2.contains(t)) because {theoremInsideForall2(x,xs,s2,t)})
  }.holds

  //This one does not verify
  def everythingContained[T](s1: List[T], s2:List[T]): Boolean = {
    decreases(s1.size)
    (s1.content == s2.content) == forall((t: T) => s1.contains(t) == s2.contains(t)) because {
      s1 match {
        case Nil() => check {(s1.content == s2.content) == forall((t: T) => s1.contains(t) == s2.contains(t))}
        case x::xs =>{
          if (s2.contains(x)) {
            ((x::xs).content == s2.content)                             ==| trivial |
            ((xs-x).content == (s2-x).content)                          ==| everythingContained(xs-x, s2-x) |
            forall((t: T) => (xs-x).contains(t) == (s2-x).contains(t))  ==| theoremInsideForall(x,xs,s2) |
            forall((t: T) => (x::xs).contains(t) == s2.contains(t))     ==| trivial |
            forall((t: T) => s1.contains(t) == s2.contains(t))
          }.qed else {
             {(s1.content == s2.content) == forall((t: T) => s1.contains(t) == s2.contains(t))}
          }
        }
      }
    }
    //(s1 == s2) == (forall((t: T) => s1.contains(t) ==> s2.contains(t)) && forall((t: T)=> s2.contains(t) ==> s1.contains(t)))
  }.holds
}

object ListOfListsForall {
  def concatListsContentLemma2[T] (l1: List[List[T]], l2: List[List[T]]): Boolean = {
    forall((x: List[T], y: List[T]) => {
      if (l1.contains(x))
        if (l2.contains(y))
          concatLists(l1,l2).contains(x++y) because {
            concatListsContentLemma(x,y,l1,l2)
          }
        else
          true
      else
        true
    })
  }.holds

  def checkl(b: Boolean): Boolean = {
    require(b)
    b
  }.holds

  //this one also can't verify
  def concatListsContentLemma[T] (x: List[T], y: List[T], l1: List[List[T]], l2: List[List[T]]): Boolean = {
    require(l1.contains(x) && l2.contains(y))
    concatLists(l1,l2).contains(x++y) == true because {
      l2 match {
        case Nil() => check{false}
        case z :: zs => if (z == y) {
          concatLists(l1,y::zs).contains(x++y) ==| trivial |
          (appendToAll(l1, y) ++ concatLists(l1 ,zs)).contains(x++y) ==| trivial |
          (appendToAll(l1, y).contains(x++y) || concatLists(l1 ,zs).contains(x++y)) ==| appendToAll(l1, y).contains(x++y) |
          true
        }.qed
        else {
          concatLists(l1,z::zs).contains(x++y) ==| trivial |
          (appendToAll(l1, z) ++ concatLists(l1 ,zs)).contains(x++y) ==| trivial |
          (appendToAll(l1, z).contains(x++y) || concatLists(l1 ,zs).contains(x++y)) ==| concatListsContentLemma(x,y,l1,zs) |
          true
        }.qed
      }
    }
  }.holds
}

import ListOfListsForall._
