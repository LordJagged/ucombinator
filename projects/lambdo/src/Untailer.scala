package org.ucombinator.project.lambdo ;

/**
 An Untailer transformation turns tail calls into non-tail calls.
 */
class Untailer {
  import LambdoSyntax._ ;
  
  private def letit (exp : Exp) : Exp = {
    val v = ExpVar(exp)
    val r = Ref(v)
    Let1(v,exp,r)
  }

  private def untailSubterms (exp : Exp) : Exp = {
    exp match {
      case e : LitExp => e
      case e : PrimOp => e
      case e : Ref => e
      
      case Lambda(params,body) => Lambda(params,t(body))

      case App(f,args) => 
        App(untailSubterms(f), args map untailSubterms)

      case If(cond,ifTrue,ifFalse) => 
        If(untailSubterms(cond),untailSubterms(ifTrue),untailSubterms(ifFalse))

      case Let1(name,value,body) =>
        Let1(name,untailSubterms(value),untailSubterms(body))

      case LetRec(names,lams,body) =>
        LetRec(names,(lams map untailSubterms) map (_.asInstanceOf[Lambda]), untailSubterms(body))

      case Set(name,exp,body) =>
        Set(name,untailSubterms(exp),untailSubterms(body))

      case Seq(List()) => VoidLit()

      case Seq(exps) => {
        val last = exps.last
        val firsts = exps.take(exps.length) map untailSubterms
        
        Seq(firsts ++ List(untailSubterms(last)))
      }        
    }
  }

  private def t (exp : Exp) : Exp = {
    exp match {
      case e : LitExp => e
      case e : PrimOp => e
      case e : Ref => e
      
      case Lambda(params,body) => 
        letit(Lambda(params,t(body)))
      
      case App(f,args) => 
        letit(App(t(f), args map t))
      
      case If(cond, ifTrue, ifFalse) => 
        If(untailSubterms(cond), t(ifTrue), t(ifFalse))

      case Let1(name,value,body) =>
        Let1(name,untailSubterms(value),t(body))

      case LetRec(names,lams,body) => 
        LetRec(names,(lams map untailSubterms) map (_.asInstanceOf[Lambda]),t(body))

      case Set(name,exp,body) =>
        Set(name,untailSubterms(exp),t(body))

      case Seq(List()) => VoidLit()

      case Seq(exps) => {
        val last = exps.last
        val firsts = exps.take(exps.length) map untailSubterms
        
        Seq(firsts ++ List(t(last)))
      }
    }
  }

  def apply(exp : Exp) : Exp = t(exp)


}
