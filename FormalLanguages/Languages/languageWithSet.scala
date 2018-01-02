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
  def concat(that: Lang[T]): Lang[T] = {
    Lang[T](this.set ++ that.set)
  }

  def contains(word: List[T]): Boolean = set.contains(word)
}

object LangSuite {
  def unitLang[T] (): Lang[T] = Lang[T](l => l.isEmpty)

  def nullLang[T](): Lang[T] = Lang[T](l => false)

  def rightUnitConcat[T](l1: Lang[T]): Boolean = {
   l1.concat(unitLang[T]) == l1
  }.holds

  def leftUnitConcat[T](l1: Lang[T]): Boolean = {
    unitLang[T].concat(l1) == l1
  }.holds


    def rightNullConcat[T](l1: Lang[T]): Boolean = {
     l1.concat(nullLang[T]) == nullLang[T]
    }.holds

    def leftNullConcat[T](l1: Lang[T]): Boolean = {
      nullLang[T].concat(l1) == nullLang[T]
    }.holds

}
