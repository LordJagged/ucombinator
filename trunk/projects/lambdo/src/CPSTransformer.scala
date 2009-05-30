package org.ucombinator.project.lambdo ;

import org.ucombinator.lang.{Extensible} ;
import org.ucombinator.util.{CPS => CPSUtil} ;


/**
 A CPSTransformer converts a program into a dialect of continuation-passing style.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.5
 
 */


class CPSTransformer {
  import LambdoSyntax._ ;

  object Cont {
    def apply(kv : Var, body : Exp) =
      Lambda(List(kv), body)

    def apply (rv : RetVar) (k : Exp => Exp) = {
      Lambda(List(rv), k(Ref(rv)))
    }

    def apply(body : Exp) = 
      Lambda(List(Var("_")), body)
  }

  private def letfresh (exp : Exp) (k : Exp => Exp) = {
    val fv = SymbolTable.fresh()
    Let1(Var(fv),exp,k(Ref(Var(fv))))
  }

  var flattenConstants = true
  var flattenVoids = true
  var flattenNums = true
  var flattenBooleans = true
  var flattenPrimOps = true
  var flattenPrimApps = true

  private def isAtomic (exp : Exp) : Boolean = exp match {    
    case Ref(_) => true
    case TextLit(_) => true
    case VoidLit() if flattenVoids => true
    case IntLit(_) if flattenNums => true
    case BoolLit(_) if flattenBooleans => true
    case _ => false
  }
  
  private def isAtomizable (exp : Exp) : Boolean = exp match {
    case PPrimOp(_) if flattenPrimOps => true
    case App(f, args) if isAtomicProcedure(f) && (args forall isAtomizable) => true
    case x if isAtomic(x) => true
    case _ => false
  }
  
  private def isAtomicProcedure (exp : Exp) : Boolean = exp match {
    case _ : PPrimOp => true
    case _ => false
  }

  import CPSConvertible._ ;

  private def a (exp : Exp) : Exp = exp match {
    case lam @ Lambda(args, body) => {
      val kv = ContVar(lam)
      (Lambda(kv :: args, tQ (body) (Ref(kv)))) setDirectStyle (lam)
    }

    case po : PrimOp => CPS(po)
    
    case App(f, args) if isAtomicProcedure(f) && (args forall isAtomizable) =>
      App(f, args map a)
    
    case x if isAtomic(x) => x

    case _ => throw new Exception("Cannot atomize: " + exp)
  }

  private def tK (exp : Exp) (k : Exp => Exp) : Exp = exp match {
    case x if isAtomic(x) => k(x)
    case x if isAtomizable(x) => k(a(x))
    case po : PrimOp => k(CPS(po))
    case Ref(_) | VoidLit() | IntLit(_) | BoolLit(_) =>
      letfresh (exp) (k)

    case lam @ Lambda(args, body) => k(a(lam))

    case App(po : PPrimOp, args) if flattenPrimApps =>
      CPSUtil.mapK (tK) (args) (args_ =>
        k(App(po, args_)))

    case App(f, args) =>
      tK (f) (f_ => 
        CPSUtil.mapK (tK) (args) (args_ =>
          App(f_, Cont (RetVar(exp)) (k) :: args_)))

    case If(cond, cons, alt) => 
      letfresh (Cont (RetVar(exp)) (k)) (qv =>
        tK (cond) (cond_ =>
          If(cond_, tQ (cons) (qv), tQ (alt) (qv))))

    case LetRec (vs, lams, body) => 
      LetRec (vs, lams map (((x : Exp) => x.asInstanceOf[Lambda]) compose a), 
              tK (body) (k))

    case Let1(v, exp, body) => 
      tQ (exp) (Cont(v, tK (body) (k)))

    case Set(v, value, body) => 
      tK (value) (value_ => 
        Set(v, value_, tK (body) (k)))

    case Seq(List()) => 
      k(VoidLit())

    case Seq(List(exp)) => 
      tK (exp) (k)

    case Seq(exp :: exps) => 
      tQ (exp) (Cont(tK (Seq(exps)) (k)))
  }

  private def tQ (exp : Exp) (q : Exp) : Exp = exp match {
    case x if isAtomic(x) => App(q, List(exp))
    case x if isAtomizable(x) => App(q, List(a(x)))
    case po : PrimOp => App(q, List(CPS(po)))
    case Ref(_) | VoidLit() | IntLit(_) | BoolLit(_) =>
      App(q,List(exp))

    case lam @ Lambda(args,body) => 
      App(q,List(a(lam)))

    case App(po : PPrimOp, args) if flattenPrimApps =>
      CPSUtil.mapK (tK) (args) (args_ =>
        letfresh (App(po, args_)) (res => 
          App(q,List(res))))

    case App(po : PPrimOp, args) =>
      CPSUtil.mapK (tK) (args) (args_ =>
        App(q,List(App(po, args_))))

    case App(f, args) =>
      tK (f) (f_ => 
        CPSUtil.mapK (tK) (args) (args_ =>
          App(f_, q :: args_)))

    case If(cond,cons,alt) => q match {
      case (Ref(_) | _ : PrimOp) => 
        tK (cond) (cond_ => 
          If (cond_, tQ (cons) (q), tQ (alt) (q)))
      case (_) => 
        letfresh (q) (qv =>
          tK (cond) (cond_ =>
            If(cond_, tQ (cons) (qv), tQ (alt) (qv))))
    }

    case LetRec (vs, lams, body) => 
      LetRec (vs, lams map (((x : Exp) => x.asInstanceOf[Lambda]) compose a), tQ (body) (q))

    case Let1(v, exp, body) => 
      tQ (exp) (Cont(v,tQ (body) (q)))
      
    case Set(v, value, body) =>
      tK (value) (value_ =>
        Set(v, value_, tQ (body) (q)))

    case Seq(List()) => 
      App(q,List(VoidLit()))

    case Seq(List(exp)) => 
      tQ (exp) (q)

    case Seq(exp :: exps) => 
      tQ (exp) (Cont(tQ (Seq(exps)) (q)))
  }

  def apply(exp : Exp) : Exp = tQ (exp) (EPrimOp("halt"))
}





/**

 A CPSConvertible object has a corresponding direct-style object from which it was converted.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.2
 */

trait CPSConvertible[A] {
  def isCPSConverted : Boolean ;
  def getDirectStyle () : A ;
  def setDirectStyle (original : A) : A ;
}



/**

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.2

 */

object CPSConvertible {

  /**
   If a Term is converted to a CPS object, then it can store the original Term in the "originalDirectStyle" field.
   */
  implicit def extensibleToCPSConvertible [A <: Extensible] (a : A) : CPSConvertible[A] = new CPSConvertible[A] {
    def isCPSConverted : Boolean = a.__properties contains ("originalDirectStyle")

    def getDirectStyle () : A = {
      a.__properties("originalDirectStyle").asInstanceOf[A]
    }

    def setDirectStyle (original : A) : A = {
      a.__properties("originalDirectStyle") = original
      a
    }
  }
}



