package org.ucombinator.project.hofa ;

import org.ucombinator.math.order.{Latticed,BoundedLattice} ;


object TransitionSystemTesting {
  var performSanityChecks = true 
}


trait Node {
  def serial : Long ;

  override def hashCode() : Int = throw new Exception("hashCode() not implemented for Node")
  override def equals(a : Any) : Boolean = throw new Exception("equals() not implemented for Node")
}


trait MonotoneNode[F,S] extends Node {

  /**
   Determines whether this state will be represented in the visited cache during state-space exploration.

   As a warning, if the exploration encounters a cycle of uncacheable
   states, it will enter an infinite loop.
  */

  def isCacheable : Boolean ;
  
  /**
   The sharp component of a state has a lattice order.
   */
  def sharp : S ;

  /**
   Produces an identical state, but with a new sharp component.

   The chief intent of this method is to allow movement up or down the lattice of approximations.
   */
  def sharp_= (sharp : S) : MonotoneNode[F,S] ;

  /**
   The flat component of a state has a flat order.
   */
  def flat : F ;
}



/**
 
 */
abstract class TransitionSystem {
  
  /**
   Nodes are states within a transition system.
   */
  type N <: Node

  /**
   Produces the neighboring states.
   */
  def succ (state : N) : List[N] ;

  /**
   Determines if a particular state is already represented in the visited cache.
   */
  def seen (state : N) : Option[N] ;

  /**
   Indicates that a state should be represented in the visited cache.
   */
  def mark (state : N) ;
  
  /**
   Moves a state up the lattice of approximation before transition.
   */
  def widen (state : N) : N ;


  /**
   Moves a state down the lattice of approximation after removal from the worklist.

   <b>Warning</b>: 
   This behavior can be unsound if not carefully reasoned.  

   Abstract garbage collection is an example of a sound narrowing.
   */
  def narrow (state : N) : N ;


  /**
   Invoked when a state transitions to a set of subsequent states.

   By default, it does nothing.
   */
  def recordTransition (state : N, next : List[N]) {
  }


  /**
   Invoked when the first state is known to be represented by the second state.

   By default, it does nothing.
   */
  def recordRepresentation (state : N, state_ : N) {
  }


  /**
   Invoked when the first state is widened into the second state.

   By default, it does nothing.
   */
  def recordWidening (state : N, state_ : N) {
  }


  /**
   Invoked when the first state is narrowed into the second state.

   By default, it does nothing.
   */
  def recordNarrowing (state : N, state_ : N) {
  }

  /**
   Counts the number of transitions taken during exploration.
   */
  var steps = 0
  

  /**
   Performs a transitive exploration of the transition system, beginning with the given states.
   */
  def explore (initStates : List[N]) {

    var todo : List[N] = initStates
    while (!todo.isEmpty) {
      var s = todo.head
      todo = todo.tail
      val s_ = narrow(s)
      recordNarrowing(s,s_)
      s = s_
      seen(s) match {
        case Some(s_) => {
          recordRepresentation(s,s_)
        }
        case None => {
          val s_ = widen(s)
          recordWidening(s,s_)
          s = s_
          mark(s)
          var next : List[N] = null
          try {
            next = (succ(s) map (_.asInstanceOf[N]))
          } catch {
            case e : Exception => {
              println("Explosion in state: " + s)
              throw e
            }
          }
          recordTransition(s,next)
          todo = next ++ todo
          steps += 1
        }  
      }
    }
  }
}



abstract class ImplicitGraph extends TransitionSystem {
  final def widen (state : N) = state
  final def narrow (state : N) = state
}





/**
 A SharpCache represents a set of Sharps.
 
 If the widen function returns an upper approximation of its argument, then this upper approximation <b>must</b> be represented in the cache.
 */
abstract class SharpCache[S <% Latticed[S]] {
  def widen (s : S) : S ;
  def mark (s : S) : Unit ;
  def represents (s : S) : Option[S] ;
}



class ListSharpCache[S <% Latticed[S]] (var isWidening : Boolean) extends SharpCache[S] {
  private var sharps : List[S] = List()

  
  def lub : S = sharps reduceLeft ((x : S, y : S) => x join y)

  def mark (s : S) {
    sharps = s :: sharps 
  }
  def widen (s : S) : S = {
    if (isWidening) {
      sharps = s :: sharps
      val max = lub
      sharps = List(max)
      max
    }
    else
      s
  }
  def represents (s : S) : Option[S] = 
    sharps find (s isWeakerThan _)
}






abstract class MonotoneTransitionSystem extends TransitionSystem {

  /* Parameters. */

  type F
  type S
  
  implicit def sharpOrder : BoundedLattice[S] ;

  type N <: MonotoneNode[F,S]
  type C <: SharpCache[S]

  protected def makeC(init : S) : C ;

  def fuse (flat : F, sharp : S) : N ;


  protected implicit def sharpToLattice (s : S) = sharpOrder.inject(s)

  private var worklist : List[N] = List()
  
  private val _cache : scala.collection.mutable.HashMap[F,C] =
    new scala.collection.mutable.HashMap[F,C]()

  private def cache(f : F) : C = {
    _cache get f match {
      case Some(cont) => cont
      case None => { val cont = makeC(sharpOrder.bot) ; _cache(f)  = cont ; cont } 
    }
  }

  def seen(state : N) : Option[N] = {
    if (!state.isCacheable)
      return None ;

    val flat = state.flat
    val sharp = state.sharp
    val cont = cache(flat)
    
    (cont represents sharp) match {
      case None => None
      case Some(sharp_) => {
        Some(fuse (flat, sharp_))
      }
    }
  }

  def mark(state : N) {
    if (!state.isCacheable) 
      return ;

    val flat = state.flat
    val sharp = state.sharp
    val container = cache(flat)
    
    container.mark(sharp)
  }


  /**
   By default, widening defers to the widening operation on the SharpContainer.
   */
  def widen(state : N) : N = {
    if (!state.isCacheable) 
      return state ;

    val flat = state.flat
    val sharp = state.sharp
    val container = cache(flat)
    
    (state.sharp = container.widen(sharp)).asInstanceOf[N]
  }


  /**
   By default, narrowing does nothing.
   */
  def narrow(state : N) : N = state
}

 
