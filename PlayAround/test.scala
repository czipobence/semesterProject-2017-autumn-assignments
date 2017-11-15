import stainless.collection._
import stainless.lang._
import stainless.proof._

object Test {
  //It's just good to know that these actually verify

  def a(i: BigInt): BigInt = {
    i+i
  }

  def b(i: BigInt): BigInt = {
    i*i
  }

  def c(i: BigInt): BigInt = {
    i - i * i
  }

  def bc(): Boolean = {
    forall((i: BigInt) => b(i) == c(i))
  }.holds

  def acbc(): Boolean = {
    forall((i: BigInt) => a(i) == b(i)) == forall((i: BigInt) => a(i) == c(i)) because {bc}
  }.holds

  def p(i: BigInt): Boolean = {
    i == BigInt(5)
  }.holds

  def q(i: BigInt): Boolean = {
    i > i*i
  }

  def pqEq():Boolean = {
    forall ((i: BigInt) => p(i) == q(i))
  }.holds

  def pqEqForall():Boolean = {
    forall ((i: BigInt) => p(i)) == forall((i: BigInt) => q(i)) because {pqEq}
  }.holds

  def insideForall(): Boolean = {
    forall ((i: BigInt) => i == BigInt(5) because {p(i)} )
  }.holds

  def doubleForall[T](p: T=> Boolean, q: T=> Boolean): Boolean = {
    forall((t:T) => p(t) == q(t)) ==> (forall((t:T) => p(t)) == forall((t:T) => q(t)))
  }.holds
}
