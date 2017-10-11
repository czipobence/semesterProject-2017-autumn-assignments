import stainless.lang._
import stainless.collection._
import stainless.proof._

case class Lang[T](set: Set[List[T]]) {

  /**
   * Here, where we explicitly specify the content for me it is not clear
   * how could we say anything about it as long as we can not iterate through
   * the set. As I see the only way would be to use set.contains as a function
   * for the "languageWithFunction" solution but in that way the solution is
   * not closer at all 
   */
  def combine(that: Lang[T]): Lang[T] = {
    Lang[T](this.set ++ that.set)
  }

  def contains(word: List[T]): Boolean = set.contains(word)
}

object LangSuite {
  def unitLang[T] (): Lang[T] = Lang[T](l => l.isEmpty)

  def nullLang[T](): Lang[T] = Lang[T](l => false)

  def rightUnitCombine[T](l1: Lang[T]): Boolean = {
   l1.combine(unitLang[T]) == l1
  }.holds

  def leftUnitCombine[T](l1: Lang[T]): Boolean = {
    unitLang[T].combine(l1) == l1
  }.holds


    def rightNullCombine[T](l1: Lang[T]): Boolean = {
     l1.combine(nullLang[T]) == nullLang[T]
    }.holds

    def leftNullCombine[T](l1: Lang[T]): Boolean = {
      nullLang[T].combine(l1) == nullLang[T]
    }.holds

}
