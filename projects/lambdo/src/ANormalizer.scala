package org.ucombinator.project.lambdo ;


import org.ucombinator.util.cps.{CPSUtil} ;


/**
 An ANormalization transformation converts an expression into an equivalent expression in which 
 */
class ANormalizer {
  import LambdoSyntax._ ;

  var flattenConstants = true
  var flattenVoids = true
  var flattenNums = true
  var flattenBooleans = true
  var flattenPrimOps = true
  var flattenPrimApps = true

  private def isAtomic (exp : Exp) : Boolean = exp match {
    case Ref(_) => true
    case VoidLit() if flattenVoids => true
    case IntLit(_) if flattenNums => true
    case BoolLit(_) if flattenBooleans => true
    case TextLit(_) => true
    case PPrimOp(_) if flattenPrimOps => true
    case App(f,args) if (flattenPrimApps && 
                         isAtomicProcedure(f) &&
                         (args forall (isAtomic))) => true
    case _ => false
  }

  private def letfresh (exp : Exp) (k : Exp => Exp) = {
    val fv = ExpVar(exp)
    Let1(fv,exp,k(Ref(fv)))
  }

  private def isAtomicProcedure (exp : Exp) : Boolean = exp match {
    case PPrimOp(p) => true
    case _ => false
  }

  // Need to walk over atamics, looking for lambdas.

  private def tK (exp : Exp) (k : Exp => Exp) : Exp = exp match {
    case (e) if isAtomic(e) => k(e)

    case Lambda(params, body) => k(Lambda(params,t (body)))

    case App(po : PrimOp, args) =>
      CPSUtil.mapK (tK) (args) (args_ =>
        k(App(po, args_)))

    case App(f, args) => 
      letfresh (CPSUtil.mapK (tK) (f::args) (fargs_ => App(fargs_.head, fargs_.tail))) (k)

    case If (cond, ifTrue, ifFalse) => 
      tK (cond) (cond_ => 
        tK (If (cond_, t(ifTrue), t(ifFalse))) (k))

    case Let1 (name, value, body) if isAtomic(value) =>
      Let1(name, value, tK (body) (k))

    case Let1 (name, value, body) =>
      Let1(name, t(value), tK (body) (k))

    case LetRec (names, lams, body) => 
      LetRec(names, lams map (((x : Exp) => x.asInstanceOf[Lambda]) compose t),
             tK (body) (k))

    case Set (name, value, body) if isAtomic(exp) =>
      Set (name, value, 
           tK (body) (k))
    
    case Set (name, value, body) =>
      letfresh (value) (value_ => 
        Set (name, value_, 
             tK (body) (k)))

    case Seq (exps) =>
      Seq (exps map (t(_)))
  }

  private def t (exp : Exp) : Exp = tK (exp) (identity)

  def apply(exp : Exp) : Exp = t(exp)
}

