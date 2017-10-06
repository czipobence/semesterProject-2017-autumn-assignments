import stainless.lang._
import stainless.collection._

object IndexConcat {

  def concatAndIndex[T](l1: List[T], l2: List[T], i: BigInt): T = {
    require (i >=0 && i < l1.size + l2.size)
    l1 match {
      case Nil() => l2(i)
      case x::xs => if (i == 0) x else concatAndIndex(xs,l2,i-1)
    }
  } ensuring { res =>
    if (i < l1.size) res == l1(i) else res == l2(i-l1.size)
  }

  //How do you explain to stainless that (x::xs ++ lst)(i) == if (x==0) x else (xs ++ ls)(i-1)
  //differently said, how do you give statements about already defined functions instead of redefining it?

  /*def concatAndIndexComplex[T](l1: List[T], l2: List[T], i: BigInt): T = {
    require (i >=0 && i < l1.size + l2.size)
    (l1 ++ l2)(i)
  } ensuring { res =>
    if (i < l1.size) res == l1(i) else res == l2(i-l1.size)
  }*/
}
