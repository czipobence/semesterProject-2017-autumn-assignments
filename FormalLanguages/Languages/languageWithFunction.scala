import stainless.lang._
import stainless.collection._
import stainless.proof._


case class Lang[T](f: List[T] => Boolean) {
    def searchSplitIter(that: Lang[T], n: BigInt, l: List[T]): Boolean = {
      require(n <= l.size && n >= 0)
      if (this.contains(l.take(n)) && that.contains(l.drop(n))) true else
      if (n == l.size) false else
      searchSplitIter(that,n+1,l)
    } ensuring { res =>
      !res ==> forall( (i: BigInt) => i <= n ==> !(this.contains(l.take(i)) && that.contains(l.drop(i))) )
    }

    def concat(that: Lang[T]): Lang[T] = {
      Lang[T](l => !forall( (i: BigInt) => !(
        i <= l.size &&
        i >= 0 &&
        this.contains(l.take(i)) &&
        that.contains(l.drop(i))
      )))
    }

    def concatTest():Boolean = {
      (Lang[Int](a => (a == List[Int](3))) concat Lang[Int](a => (a == List[Int](5))) ).contains(List[Int](5,3))
    }.holds

    def ++(that: Lang[T]): Lang[T] = {
      Lang[T](w => this.f(w) || that.f(w))
    }

    // How could we define equality otherwise, there is no way that this would verify
    // x => f(x) =? x => exists n. f(x.take(n)) && unit(x.drop(n))
    def isEqual (that: Lang[T]): Boolean = {
      forall ( (x: List[T]) => this.contains(x) ==> that.contains(x) ) &&
      forall ( (x: List[T]) => that.contains(x) ==> this.contains(x) )
      //maybe forall ( (x: List[T]) => this.contains(x) == that.contains(x) ) but thats nto easier for the solver
    }

  def contains(word: List[T]): Boolean = f(word)
}

object LangSuite {
  def unitLang[T] (): Lang[T] = Lang[T](l => l.isEmpty)

  def nullLang[T](): Lang[T] = Lang[T](l => false)

  def rightUnitConcat[T](l1: Lang[T]): Boolean = {
    l1.concat(unitLang[T]()) isEqual l1
  }.holds

  def leftUnitConcat[T](l1: Lang[T]): Boolean = {
    unitLang[T]().concat(l1) isEqual l1
  }.holds


  def rightNullConcat[T](l1: Lang[T]): Boolean = {
    l1.concat(nullLang[T]()) isEqual nullLang[T]()
  }.holds

  def leftNullConcat[T](l1: Lang[T]): Boolean = {
    nullLang[T]().concat(l1) isEqual nullLang[T]()
  }.holds
}
