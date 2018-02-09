import stainless.lang._
import stainless.collection._

object IndexConcat {
  // Concatenation of words w and v has letters w1,w2,..., wn, v1,v2,...,vm
  // (wv)[i] == w[i] if i <=n otherwise it is v[i-n]
  def concatAndIndex[T](l1: List[T], l2: List[T], i: BigInt): T = {
    require (i >=0 && i < l1.size + l2.size)
    l1 match {
      case Nil() => l2(i)
      case x::xs => if (i == 0) x else concatAndIndex(xs,l2,i-1)
    }
  } ensuring { res =>
    if (i < l1.size) res == l1(i) else res == l2(i-l1.size)
  }

}
