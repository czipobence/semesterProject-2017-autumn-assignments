import stainless.lang._
import stainless.collection._
import stainless.proof._


case class Lang[T](f: List[T] => Boolean) {
    def searchSplitIter(that: Lang[T], n: BigInt, l: List[T]): Boolean = {
      require(n <= l.size && n >= 0)
      if (this.contains(l.take(n)) && that.contains(l.drop(n))) true else
      if (n == 0) false else
      searchSplitIter(that,n-1,l)
    }

    def combine(that: Lang[T]): Lang[T] = {
      Lang[T](l => searchSplitIter(that, l.size, l))
    }.ensuring {res =>
      forall((t1: List[T]) => this.contains(t1) ==> forall((t2: List[T]) => that.contains(t2) ==> res.contains(t1 ++ t2)) )
    }

    // How could we define equality otherwise, there is no way that this would verify
    // x => f(x) =? x => exists n. f(x.take(n)) && unit(x.drop(n))  
    def == (that: Lang[T]): Lang[T] = {
      forall ( (x: List[T]) => this.contains(x) ==> that.contains(x) ) &&
      forall ( (x: List[T]) => that.contains(x) ==> this.contains(x) )
    }

  def contains(word: List[T]): Boolean = f(word)
}

object LangSuite {
  def unitLang[T] (): Lang[T] = Lang[T](l => l.isEmpty)

  def nullLang[T](): Lang[T] = Lang[T](l => false)

  def rightUnitCombine[T](l1: Lang[T]): Boolean = {
    l1.combine(unitLang[T]()) == l1
  }

  def leftUnitCombine[T](l1: Lang[T]): Boolean = {
    unitLang[T]().combine(l1) == l1
  }


  def rightNullCombine[T](l1: Lang[T]): Boolean = {
    l1.combine(nullLang[T]()) == nullLang[T]()
  }

  def leftNullCombine[T](l1: Lang[T]): Boolean = {
    nullLang[T]().combine(l1) == nullLang[T]()
  }
}
