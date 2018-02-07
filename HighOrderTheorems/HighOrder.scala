import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

/**
 * This code snippet is to test if Stainless can verify theorems about functions
 * I called them High Order Theorems after high order function (map, foldr,...)
 */

object HighOrder {

  // If the order of two operations are interchangeable in case of two
  // paramaters, so does it in case of three.
  def commutativityTheorem[T](f: T => T, g: (T,T) => T): Boolean = {
    require(forall((a: T, b: T) => f(g(a,b)) == g(f(a), f(b))  )  )
    forall((a: T, b: T, c: T) => f(g(g(a,b),c)) == g(g(f(a), f(b)), f(c))  )
  }.holds
}

// A structure with two operations
object SampleStructure {
    // The one argument operation. First I experimented with identity, but
    // then Stainless could verify it on its own so I tweaked it a bit, however,
    // the name remains
    def identity(a: List[BigInt]): List[BigInt] = {
      a match {
        case Nil() => Nil()
        case x :: xs => (x + 1) :: identity(xs)
      }
    }

    // Two argument operation (g)
    def concat[T](a: List[T], b: List[T]) = {
      a ++ b
    }

    // Theorem about the interchangeabilty of the order of operations
    @induct
    def concatIdentityDistributive(a: List[BigInt], b: List[BigInt]): Boolean = {
      (identity(concat(a,b)) == concat(identity(a), identity(b)))
    }.holds

}

import HighOrder._
import SampleStructure._

// Example how this could be used to prove a real lemma
object Demo {
  def useHighOrderTheorem(a: List[BigInt], b: List[BigInt], c: List[BigInt]): Boolean = {
    check {forall((a: List[BigInt], b: List[BigInt]) => identity(concat(a,b)) == concat(identity(a), identity(b)) because {concatIdentityDistributive(a,b)})}
    identity(concat(concat(a,b),c)) == concat(concat(identity(a), identity(b)), identity (c)) because {
      commutativityTheorem[List[BigInt]](identity, concat)
    }
  }.holds
}
