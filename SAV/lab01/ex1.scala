object Bank1 {
  case class Acc(checking : BigInt, savings : BigInt)

  def putAside(x: BigInt, a: Acc): Acc = {
    require (notRed(a) && a.checking >= x && x>0)
    Acc(a.checking - x, a.savings + x)
  } ensuring {
    r => notRed(r) && sameTotal(a, r)
  }


  def sameTotal(a1: Acc, a2: Acc): Boolean = {
    a1.checking + a1.savings == a2.checking + a2.savings
  }

  def notRed(a: Acc) : Boolean = {
    a.checking >= 0 && a.savings >= 0
  }
}
