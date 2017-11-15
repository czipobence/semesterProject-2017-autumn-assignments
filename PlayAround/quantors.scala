import stainless.collection._
import stainless.lang._
import stainless.proof._

object Existential {
  def exists[A](p: A => Boolean): Boolean = !forall((x: A) => !p(x))
  def exists[A, B](p: (A,B) => Boolean): Boolean = !forall((x: A,y: B) => !p(x,y))
  def exists[A, B, C](p: (A,B,C) => Boolean): Boolean = !forall((x: A,y: B, z: C) => !p(x,y,z))
  def exists[A, B, C, D](p: (A,B,C,D) => Boolean): Boolean = !forall((x: A,y: B, z: C, w: D) => !p(x,y,z,w))
}

import Existential._

object Quantors {
  def test[T](a: T, b: T, f: T => Boolean):Boolean = {
    ((a == b) && f(a)) == ((a == b) && f(b))
  }.holds

  def test2[T](a: List[T], x: List[T], y: List[T], z: List[T], xy: List[T] ):Boolean = {
    ((xy == (x ++ y)) && (a == (xy ++ z))) == ((xy == (x ++ y)) && (a == ((x ++ y) ++ z))) because {
      test(xy, x ++ y, (i: List[T]) => (a == (i ++ z)) )
    }
  }.holds

  def test2Forall[T](a: List[T]): Boolean = {
    forall ((xy: List[T], z: List[T], x: List[T], y: List[T]) => ((xy == (x ++ y)) && (a == (xy ++ z))) == ((xy == (x ++ y)) && (a == ((x ++ y) ++ z))) because {test2(a,x,y,z,xy)})
  }

  def replaceInExist[T](f: T => Boolean, g: T=> Boolean) = {
    require(forall((t: T) =>  f(t) == g(t)))
    exists((t:T) => f(t)) == exists((t:T) => g(t))
  }.holds

  def replaceInForall[T](f: T => Boolean, g: T=> Boolean) = {
    require(forall((t: T) =>  f(t) == g(t)))
    forall((t:T) => f(t)) == forall((t:T) => g(t))
  }.holds

  def random[T](l1: List[List[T]], l2: List[List[T]], l3: List[List[T]], a: List[T]):Boolean = {
    check {
      exists[List[T], List[T]]((xy: List[T], z: List[T]) => {
        exists[List[T], List[T]] ((x: List[T], y: List[T]) => {
          l1.contains(x) && l2.contains(y) && (xy == (x ++ y))
        }) && l3.contains(z) && (a == (xy ++ z))
      }) ==
        exists[List[T], List[T]]((xy: List[T], z: List[T]) => {
          exists[List[T], List[T]] ((x: List[T], y: List[T]) => {
            l1.contains(x) && l2.contains(y) && (xy == (x ++ y)) && l3.contains(z) && (a == (xy ++ z))
          })
        })
      } && check {
        exists[List[T], List[T]]((xy: List[T], z: List[T]) => {
          exists[List[T], List[T]] ((x: List[T], y: List[T]) => {
            l1.contains(x) && l2.contains(y) && (xy == (x ++ y)) && l3.contains(z) && (a == (xy ++ z))
          })
        }) ==
        exists[List[T], List[T]]((xy: List[T], z: List[T]) => {
          exists[List[T], List[T]] ((x: List[T], y: List[T]) => {
            l1.contains(x) && l2.contains(y) && l3.contains(z) && ((xy == (x ++ y)) && (a == (xy ++ z)))
          })
        })
      } && check {
        exists[List[T], List[T]]((xy: List[T], z: List[T]) => {
          exists[List[T], List[T]] ((x: List[T], y: List[T]) => {
            l1.contains(x) && l2.contains(y) && l3.contains(z) && ((xy == (x ++ y)) && (a == (xy ++ z)))
          })
        }) ==
        exists[List[T], List[T], List[T], List[T]]((xy: List[T], z: List[T], x: List[T], y: List[T]) => {
          l1.contains(x) && l2.contains(y) && l3.contains(z) && ((xy == (x ++ y)) && (a == (xy ++ z)))
        })
      } && check {
        exists[List[T], List[T], List[T], List[T]]((xy: List[T], z: List[T], x: List[T], y: List[T]) => {
          l1.contains(x) && l2.contains(y) && l3.contains(z) && ((xy == (x ++ y)) && (a == (xy ++ z)))
        }) ==
        exists[List[T], List[T], List[T], List[T]]((xy: List[T], z: List[T], x: List[T], y: List[T]) => {
          l1.contains(x) && l2.contains(y) && l3.contains(z) && ((xy == (x ++ y)) && (a == ((x++y) ++ z)))
        }) because {
          test2Forall(a)
        }
      } && check {
        exists[List[T], List[T], List[T], List[T]]((xy: List[T], z: List[T], x: List[T], y: List[T]) => {
          l1.contains(x) && l2.contains(y) && l3.contains(z) && ((xy == (x ++ y)) && (a == (xy ++ z)))
        }) ==
        exists[List[T], List[T], List[T], List[T]]((z: List[T], x: List[T], y: List[T]) => {
          l1.contains(x) && l2.contains(y) && l3.contains(z) && ((a == ((x++y) ++ z)))
        })
      }
  }.holds

  //revrite the property as a function that return a boolean
}
