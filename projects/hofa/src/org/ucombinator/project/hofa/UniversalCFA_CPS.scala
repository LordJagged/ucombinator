package org.ucombinator.project.hofa ; 

import org.ucombinator.project.lambdo._ ;

import org.ucombinator.languages.sexp._ ;
import org.ucombinator.languages.json._ ;
import org.ucombinator.math.order._ ;




abstract class UniversalCFA_CPS extends UniversalCFAFramework {

  import AbstractCommon._
  import LambdoSyntax._



  /**
   Selects a new abstract context when evaluating the procedure proc.
   */
  def nextContext (proc : Val, state : EvalState) : K ;

  /**
   Selects a new abstract context when applying a procedure.
   */
  def nextContext (state : ApplyState) : K ;

  /**
   Selects a new abstract context when moving through an evaluation.
   */
  def nextContext (state : EvalState) : K ;

  /**
   Selects a new abstract context when moving through a conditional branch.
   */
  def nextContext (cond : Boolean, state : EvalState) : K ;

  /**
   Allocates locatives for the supplied variables during procedure application.
   */
  def alloc (vars : List[Var], state : ApplyState) : List[Loc] ;

  /**
   Allocates locatives for the supplied variables during evaluation.
   */
  def alloc (vars : List[Var], state : EvalState) : List[Loc] ;


  /**
   Determines whether contexts are part of the flat-space or not.
   */
  var cacheContexts = true


  /* Mechanics. */
  private [hofa] case class EvalFlat (val call : Exp, val bEnv : BEnv, val k : K) extends Flat {
    override def hashCode() : Int = 
      (if (cacheContexts) { k.hashCode() * 3 } else 0) + call.hashCode() * 2 + bEnv.hashCode() 
    override def equals(a : Any) : Boolean = a match {
      case EvalFlat(call2, bEnv2, k2) => (call equals call2) && (bEnv equals bEnv2) && (!cacheContexts || (k equals k2))
      case _ => false
    }
  }
  private [hofa] case class ApplyFlat (val proc : Val, val dvec : List[D], val k : K) extends Flat {
    private lazy val dvecHashCode = dvec.foldRight (0) (_.hashCode() + 2*_)

    override def hashCode() : Int = 
      (if (cacheContexts) { k.hashCode() * 3 } else 0) + proc.hashCode() * 2 + dvecHashCode
    override def equals(a : Any) : Boolean = a match {
      case ApplyFlat(proc2, dvec2, k2) => (proc equals proc) && (dvec.equalsWith(dvec2)(_ equals _)) && (!cacheContexts || (k equals k2))
      case _ => false
    }
  }




  
  case class EvalState(val call : Exp, val bEnv : BEnv, val store : Store, val k : K) extends AbstractState {
    val isCacheable = true
    val isGarbageCollectable = true

    def store_= (store_ : Store) : EvalState = EvalState(call,bEnv,store_,k)

    override def touches = bEnv.toMap.toList map (binding => LocNode(binding._2))

    def flat : Flat = EvalFlat(call,bEnv,k)
    def sharp : Sharp = Sharp(store)
    def sharp_= (s : Sharp) : EvalState = EvalState(call,bEnv,s.store,k)

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      F("EvalState",List(O(Map("call" -> call.toJSON(),
                               "bEnv" -> bEnv.toJSON(),
                               "store" -> store.toJSON(),
                               "k" -> k.toJSON()))))
    }
  }

  case class ApplyState(val proc : Val, val dvec : List[D], val store : Store, val k : K) extends AbstractState {
    val isCacheable = false
    val isGarbageCollectable = false

    def store_= (store_ : Store) : ApplyState = ApplyState(proc,dvec,store_,k)

    def flat : Flat = ApplyFlat(proc,dvec,k)
    def sharp : Sharp = Sharp(store)
    def sharp_= (s : Sharp) : ApplyState = ApplyState(proc,dvec,s.store,k)

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      F("ApplyState",List(O(Map("proc" -> proc.toJSON(),
                                "dvec" -> JSON.fromIterable(dvec),
                                "store" -> store.toJSON(),
                                "k" -> k.toJSON()))))
    }
  }





  /* Satisfying MonotoneTransitionSystem requirements. */
  type C = ListSharpCache[S]
  protected def makeC(init : S) = new ListSharpCache[S](usePerFlatWidening)

  def fuse (flat : F, sharp : S) : N = flat match {
    case EvalFlat(call,bEnv,k) => EvalState(call, bEnv, sharp.store, k)
    case ApplyFlat(proc,dvec,k) => ApplyState(proc,dvec,sharp.store,k)
  }

  def succ(state : N) : List[N] = state match {

    case s @ EvalState(App(f,args),be,store,k) => {
      val argVals = args map (atomEval (be,store) _)
      for (proc <- (atomEval (be,store) (f)).toList if proc.isInstanceOf[Proc]) yield {
        val k_ = nextContext(proc,s)
        ApplyState(proc, argVals, store, k_) 
      }
    }

    case s @ EvalState(If(cond,ifTrue,ifFalse),bEnv,store,k) => {
      val kTrue = nextContext(true,s)
      val kFalse = nextContext(false,s)
      List(EvalState(ifTrue,bEnv,store,kTrue),
           EvalState(ifFalse,bEnv,store,kFalse))
    }

    case s @ EvalState(Set(v,e,body),bEnv,store,k) => {
      val k_ = nextContext(s)
      val argVal = atomEval (bEnv,store) (e)
      val addr = bEnv(v)
      val store_ = store + (addr,argVal)
      List(EvalState(body,bEnv,store_,k_))
    }

    case s @ EvalState(LetRec(vars,lams,body),bEnv,store,k) => {
      val k_ = nextContext(s)
      
      val addrs = alloc(vars,s)
      val varsXaddrs = vars zip addrs
      val bEnv_ = bEnv ++ varsXaddrs
      val cloVals = lams map (atomEval (bEnv_,store))
      
      val addrsXvals = addrs zip cloVals
      val store_ = store ++ addrsXvals

      List(EvalState(body,bEnv_,store_,k_))
    }

    case s @ ApplyState(Clo(Lambda(vars,body),bEnv), argVals, store, k) if vars.length == argVals.length => {
      val k_ = nextContext(s)

      val addrs = alloc(vars,s)

      val varsXaddrs = vars zip addrs
      val addrsXvals = addrs zip argVals
      
      val bEnv_ = bEnv ++ varsXaddrs
      val store_ = store ++ addrsXvals

      List(EvalState(body,bEnv_,store_,k_))
    }

    case s @ ApplyState(Clo(Lambda(vars,body),bEnv), argVals, store, k) if vars.length != argVals.length => 
      List()

    case ApplyState(Op(EPrimOp("halt")),_,_,_) => List()

    case unmatched => {
      throw new Exception("Code incomplete; state unmatched:\n " + unmatched)
    }
  }

}






class `0CFA_CPS` extends UniversalCFA_CPS {

  import LambdoSyntax._
  import AbstractCommon._

  def botBEnv = StandardDomains.botBEnv
  def botStore = StandardDomains.botStore
  def botD = StandardDomains.botD

  type K = AbstractCommon.Context


  def alloc (vars : List[Var], state : ApplyState) : List[Loc] =
    vars map (VarLoc(_))
  def alloc (vars : List[Var], state : EvalState) : List[Loc] =
    vars map (VarLoc(_))

  def nextContext (s : ApplyState) = AbstractCommon.MonoContext
  def nextContext (proc : Val, s : EvalState) = AbstractCommon.MonoContext
  def nextContext (s : EvalState) = AbstractCommon.MonoContext
  def nextContext (cond : Boolean, s : EvalState) = AbstractCommon.MonoContext


  def explore (call : Exp) {
    val initState = EvalState(call,botBEnv,botStore,AbstractCommon.MonoContext)
    explore(List(initState))
  }

}
