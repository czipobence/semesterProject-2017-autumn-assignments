import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

object HighOrder {
  def commutativityTheorem[T](f: T => T, g: (T,T) => T): Boolean = {
    require(forall((a: T, b: T) => f(g(a,b)) == g(f(a), f(b))  )  )
    forall((a: T, b: T, c: T) => f(g(g(a,b),c)) == g(g(f(a), f(b)), f(c))  )
  }.holds

  def identity(a: List[BigInt]): List[BigInt] = {
    a match {
      case Nil() => Nil()
      case x :: xs => (x + 1) :: identity(xs)
    }
  }

  def concat[T](a: List[T], b: List[T]) = {
    a ++ b
  }

  def concatIdentityDistributive(a: List[BigInt], b: List[BigInt]): Boolean = {
    identity(concat(a,b)) == concat(identity(a), identity(b))
  }.holds


  def concatIdentityDistributiveForall(): Boolean = {
    forall((a: List[BigInt], b: List[BigInt]) => identity(concat(a,b)) == concat(identity(a), identity(b)) because {concatIdentityDistributive(a,b)})
  }.holds

  def useHighOrderTheorem(a: List[BigInt], b: List[BigInt], c: List[BigInt]): Boolean = {
    identity(concat(concat(a,b),c)) == concat(concat(identity(a), identity(b)), identity (c)) because {
      commutativityTheorem[List[BigInt]](identity, concat) because {concatIdentityDistributiveForall()}
    }
  }.holds
}
