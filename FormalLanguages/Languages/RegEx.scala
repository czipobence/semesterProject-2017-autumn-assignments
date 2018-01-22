import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

//Regex expressions and proofs about them

// we rely on lang
import Lang._
import LangSpecs._

sealed abstract class RegEx {
  //evaluate the regular expression to a language
  def eval[T](l1: Lang[T], l2: Lang[T]): Lang[T]

  //find a suitable n:BigInt such that (L1 ++ L2) ^ n is a superset of the evaluation of the regex
  def evalExp(): BigInt
}

object Max {
    def max(x: BigInt, y: BigInt): BigInt = {if (x >= y) x else y} ensuring {res => res >= x && res >= y}
}

import Max._

case class L1() extends RegEx {
  override def eval[T](l1: Lang[T], l2: Lang[T]): Lang[T] = l1
  override def evalExp(): BigInt = BigInt(1)
}

case class L2() extends RegEx {
  override def eval[T](l1: Lang[T], l2: Lang[T]): Lang[T] = l2
  override def evalExp(): BigInt = BigInt(1)
}

case class Union(left: RegEx, right: RegEx) extends RegEx {
  override def eval[T](l1: Lang[T], l2: Lang[T]): Lang[T] = (left.eval(l1, l2) ++ right.eval(l1, l2))
  override def evalExp(): BigInt = max(left.evalExp(), right.evalExp())
}

case class Conc(left: RegEx, right: RegEx) extends RegEx {
  override def eval[T](l1: Lang[T], l2: Lang[T]): Lang[T] = (left.eval(l1, l2) concat right.eval(l1, l2))
  override def evalExp(): BigInt = left.evalExp() + right.evalExp()
}

//This case is not crucial, as Pow(r,n) = Conc(r, pow(r, n-1))
/*
case class Pow(expr: RegEx, pow: BigInt) extends RegEx {
  require(pow >= BigInt(0))
  override def eval[T](l1: Lang[T], l2: Lang[T]): Lang[T] = (expr.eval(l1, l2) ^ pow)
  override def evalExp(): BigInt = (expr.evalExp() * pow)
}*/

object RegExSpecs {

  //proof that the exponent is always positive
  def evalExpPositive(expr: RegEx): Boolean = {
    expr.evalExp() >= BigInt(0) because {
      expr match {
        case L1() => check{L1().evalExp == BigInt(1)}
        case L2() => check{L2().evalExp == BigInt(1)}
        case Union(left, right) => {
          //for some reason stainless found them as counterexample if they are not checked
          check {Union(L1(),L1()).evalExp() == BigInt(1)} &&
          check {Union(L2(),L2()).evalExp() == BigInt(1)} &&
          check {left.evalExp() >= BigInt(0) because evalExpPositive(left)} &&
          check {right.evalExp() >= BigInt(0) because evalExpPositive(right)}
        }
        case Conc(left, right) => {
          //for some reason stainless found them as counterexample if they are not checked
            check {Conc(L1(),L1()).evalExp() == BigInt(2)} &&
            check {Conc(L2(),L2()).evalExp() == BigInt(2)} &&
            check {left.evalExp() >= BigInt(0) because evalExpPositive(left)} &&
            check {right.evalExp() >= BigInt(0) because evalExpPositive(right)}
        }
        /*case Pow(e, p) => {
            //for some reason stainless found them as counterexample if they are not checked
            check {Pow(L1(),BigInt(0)).evalExp() == BigInt(0)} &&
            check {e.evalExp() >= BigInt(0) because evalExpPositive(e)} &&
            check {p >= BigInt(0)}
        }*/
      }
    }
  }.holds

  @library
  def regexSubsetStar[T](expr: RegEx, l1: Lang[T], l2: Lang[T]): Boolean = {
    check {expr.evalExp() >= BigInt(0) because {evalExpPositive(expr) }}
    expr.eval(l1, l2) subsetOf ((l1 ++ l2) close expr.evalExp()) because {
      expr match {
        case L1() => {
          check {L1().eval(l1,l2) == l1} &&
          check {L1().evalExp() == BigInt(1)} &&
          check {l1 subsetOf ((l1++l2) close BigInt(1)) because {
            check {((l1++l2) ^ BigInt(1)) sameAs (l1 ++ l2) because {langToFirst(l1++l2)}} &&
            check {l1 subsetOf (l1 ++ l2)} &&
            sameAsSubsetTrans(l1, (l1++l2),(l1++l2) ^ BigInt(1))
          }}
        }
        case L2() => {
          check {L2().eval(l1,l2) == l2} &&
          check {L2().evalExp() == BigInt(1)} &&
          check {l2 subsetOf ((l1++l2) close BigInt(1)) because {
            check {((l1++l2) ^ BigInt(1)) sameAs (l1 ++ l2) because {langToFirst(l1++l2)}} &&
            check {l2 subsetOf (l1 ++ l2)} &&
            sameAsSubsetTrans(l2, (l1++l2),(l1++l2) ^ BigInt(1))
          }}
        }
        case Union(left, right) => {
          check {expr.eval(l1, l2) == (left.eval(l1, l2) ++ right.eval(l1, l2))} && //this step fails
          check {(expr.eval(l1, l2) subsetOf ((l1 ++ l2) close expr.evalExp())) == ((left.eval(l1, l2) ++ right.eval(l1, l2)) subsetOf ((l1 ++ l2) close expr.evalExp()))} &&
          check {((left.eval(l1, l2) ++ right.eval(l1, l2)) subsetOf ((l1 ++ l2) close expr.evalExp())) == ((left.eval(l1, l2) ++ right.eval(l1, l2)) subsetOf ((l1 ++ l2) close max(left.evalExp(), right.evalExp())))} &&
          check {((left.eval(l1, l2) ++ right.eval(l1, l2)) subsetOf ((l1 ++ l2) close max(left.evalExp(), right.evalExp()))) == (( (left.eval(l1, l2) subsetOf ((l1++l2) close max(left.evalExp(), right.evalExp())) ) && (right.eval(l1, l2) subsetOf ((l1++l2) close max(left.evalExp(), right.evalExp())) ) ))} &&
          check {
            left.eval(l1, l2) subsetOf ((l1++l2) close max(left.evalExp(), right.evalExp())) because {
              check {left.eval(l1, l2) subsetOf ((l1++l2) close left.evalExp()) because {
                regexSubsetStar(left,l1,l2)
              }} &&
              check {
                ((l1++l2) close left.evalExp()) subsetOf ((l1++l2) close max(left.evalExp(), right.evalExp())) because {
                  subsetCloseLe((l1++l2), left.evalExp(), max(left.evalExp(), right.evalExp()))
                }
              }
            }
          } &&
          check {
            right.eval(l1, l2) subsetOf ((l1++l2) close max(left.evalExp(), right.evalExp())) because {
              check {right.eval(l1, l2) subsetOf ((l1++l2) close right.evalExp()) because {
                regexSubsetStar(right,l1,l2)
              }} &&
              check {
                ((l1++l2) close right.evalExp()) subsetOf ((l1++l2) close max(left.evalExp(), right.evalExp())) because {
                  subsetCloseLe((l1++l2), right.evalExp(), max(left.evalExp(), right.evalExp()))
                }
              }
            }
          } &&
          check {expr.eval(l1, l2) subsetOf ((l1 ++ l2) close expr.evalExp())}
        }
        case Conc(left, right) => {
          check {(expr.eval(l1, l2) subsetOf ((l1 ++ l2) close expr.evalExp())) == ((left.eval(l1, l2) concat right.eval(l1, l2)) subsetOf ((l1 ++ l2) close expr.evalExp()))} && //this step fails
          check {((left.eval(l1, l2) concat right.eval(l1, l2)) subsetOf ((l1 ++ l2) close expr.evalExp())) == ((left.eval(l1, l2) concat right.eval(l1, l2)) subsetOf ((l1 ++ l2) close (left.evalExp() + right.evalExp())))}
          check {((left.eval(l1, l2) concat right.eval(l1, l2)) subsetOf ((l1 ++ l2) close (left.evalExp() + right.evalExp()))) because {
            check {(left.eval(l1, l2) concat right.eval(l1, l2)) subsetOf (((l1++l2) close (left.evalExp())) concat right.eval(l1, l2)) because {
              regexSubsetStar(left,l1,l2) &&
              concatSubset(left.eval(l1, l2), (l1++l2) close (left.evalExp()),right.eval(l1, l2))
            }} &&
            check {(((l1++l2) close (left.evalExp())) concat right.eval(l1, l2)) subsetOf (((l1++l2) close (left.evalExp())) concat ((l1++l2) close (right.evalExp()))) because {
              regexSubsetStar(right,l1,l2) &&
              concatSubset2((l1++l2) close (left.evalExp()),right.eval(l1, l2), (l1++l2) close (right.evalExp()))
            }} &&
            check {(((l1++l2) close (left.evalExp())) concat ((l1++l2) close (right.evalExp()))) subsetOf ((l1 ++ l2) close (left.evalExp() + right.evalExp())) because {sumClose(l1++l2, left.evalExp, right.evalExp)}}
          }} &&
          check {expr.eval(l1, l2) subsetOf ((l1 ++ l2) close expr.evalExp())}
        }
        /*case Pow(e,p) => {
          p match {
            case BigInt(0) => {
              check{expr.evalExp() == BigInt(0) because {
                check {expr.evalExp() == (e.evalExp() * BigInt(0))} &&
                check {(e.evalExp() * BigInt(0)) == BigInt()}
              }}
              check{(e.eval(l1, l2) ^ BigInt(0)) == Lang.unitLang[T]()}
              check{((l1 ++ l2) close BigInt(0)) == Lang.unitLang[T]()}
              check{(e.eval(l1, l2) ^ BigInt(0)) subsetOf ((l1 ++ l2) close BigInt(0))}
            }
            case _ => {
              check {expr.eval(l1, l2) sameAs ((e.eval(l1,l2)) ^ p )} &&
              check {((e.eval(l1,l2)) ^ p ) sameAs ((e.eval(l1,l2)) concat (e.eval(l1,l2) ^ (p-1)))} &&
              check {((e.eval(l1,l2)) concat (e.eval(l1,l2) ^ (p-1))) subsetOf ((e.eval(l1,l2)) concat ((l1++l2) close (e.evalExp() * (p-1)))) because {
                check {(e.eval(l1,l2) ^ (p-1)) sameAs Pow(e,p-1).eval(l1,l2)} &&
                check {(e.eval(l1,l2) ^ (p-1)) subsetOf ((l1 ++ l2) close (e.evalExp() * (p-1))) because {
                  regexSubsetStar(Pow(e,p-1), l1, l2)
                }} &&
                concatSubset2(e.eval(l1,l2), e.eval(l1,l2) ^ (p-1), (l1++l2) close (e.evalExp() * (p-1)))
              }} &&
              check {((e.eval(l1,l2)) concat ((l1++l2) close (e.evalExp() * (p-1)))) subsetOf (((l1++l2) close e.evalExp()) concat ((l1++l2) close (e.evalExp() * (p-1)))) because {
                regexSubsetStar(e, l1, l2) &&
                check{e.evalExp() >= BigInt(0) because evalExpPositive(e)}
                concatSubset(e.eval(l1,l2), (l1++l2) close e.evalExp(), (l1++l2) close (e.evalExp() * (p-1)))
              }} &&
              check {(((l1++l2) close e.evalExp()) concat ((l1++l2) close (e.evalExp() * (p-1)))) subsetOf ((l1++l2) close (e.evalExp() + (e.evalExp() * (p-1)))) because {
                check {sumClose(l1++l2, e.evalExp(), e.evalExp() * (p-1))}
              }} &&
              check {((l1++l2) close (e.evalExp() + (e.evalExp() * (p-1)))) sameAs ((l1++l2) close (e.evalExp() * p))} &&
              check {expr.eval(l1, l2) subsetOf ((l1 ++ l2) close expr.evalExp())}

            }
          }
        }*/
      }
    }
  }.holds
}
