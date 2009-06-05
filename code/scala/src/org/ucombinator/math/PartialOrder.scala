package org.ucombinator.math.order ;

/**
 When two objects, a and b, are related under an ordering, there are four cases:
 <ol>
  <li>(LT) a is strictly less than b;</li>
  <li>(GT) a is strictly greater than b;</li>
  <li>(EQ) a is equal to b; and</li>
  <li>(NA) a is incomparable with b.</li>
 </ol>

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 1.0

*/
sealed abstract class PartialOrdering

/**
 Less than.
 */
final case object LT extends PartialOrdering

/**
 Equal.
*/
final case object EQ extends PartialOrdering

/**
 Greater than.
 */
final case object GT extends PartialOrdering

/**
 Incomparable.
 */
final case object NA extends PartialOrdering



/**
 A PartialOrder for type A permits two A's to be compared.

 If either partialCompare or weakerThan is overriden, then the rest
 of the methods function properly.

 If neither is overriden, invocation of either will lead to infinite
 recursion.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9
 */
trait PartialOrder[A] {

  /**
   Returns the relative ordering of x and y.
   */
  def partialCompare (x : A, y : A) : PartialOrdering = {
    val xLTEy = weakerThan(x,y)
    val yLTEx = weakerThan(y,x)
    (xLTEy,yLTEx) match {
      case (true,true) => EQ
      case (true,false) => LT
      case (false,true) => GT
      case (false,false) => NA
    }
  }

  /**
   Return true if and only if x is less than or equal to y.
   */
  def weakerThan (x : A, y : A) : Boolean = 
    partialCompare (x ,y) match {
      case EQ => true
      case LT => true
      case GT => false
      case NA => false
    }

  /**
   Returns true if and only if x is (strictly) less than y.
   */
  def strictlyWeakerThan (x : A, y : A) : Boolean = 
    partialCompare (x ,y) match {
      case EQ => false
      case LT => true
      case GT => false
      case NA => false
    }

  private val poset = this

  /**
   Injects a compatible object into the partial order. (Useful for creating implicits.)
   */
  def inject[B <% A] (x : B) : PartiallyOrdered[A] = new PartiallyOrdered[A] {
    def partialCompare(y : A) = poset.partialCompare(x, y)
  }


}


/**
 An object is partially ordered with respect to a set A if it provides
 a comparison operation.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9
 */
trait PartiallyOrdered[A] {
  def partialCompare (y : A) : PartialOrdering ;
  def isWeakerThan (y : A) : Boolean = partialCompare(y) match {
      case EQ => true
      case LT => true
      case GT => false
      case NA => false
  }
}

/**

 In a join semi-lattice, any two elements must have a least upper
 bound, as computed by the join method.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

 */
trait JoinSemiLattice[A] extends PartialOrder[A] {
  /**
   Returns the least upper bound of two objects, if known and computable.
   */
  def join (x : A, y : A) : A = partialCompare (x,y) match {
    case EQ => x
    case LT => y
    case GT => x
    case NA => throw new UnknownLUBException(x,y)
  }  
}

/**
 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9
*/
trait JoinSemiLatticed[A] extends PartiallyOrdered[A] {
  def join (y : A) : A ;
}


/**
 
 In a meet semi-lattice, any two elements must have a greatest lower
 bound, as computed by the join method.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

 */
trait MeetSemiLattice[A] extends PartialOrder[A] {
  /**
   Returns the greatest lower bound of two objects, if known and computable.
   */
  def meet (x : A, y : A) : A = (partialCompare (x,y)) match {
    case EQ => x
    case LT => x
    case GT => y
    case NA => throw new UnknownGLBException(x,y)
  }  
}


/**
 
 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

*/
trait MeetSemiLatticed[A] extends PartiallyOrdered[A] {
  def meet (y : A) : A ;
}



/**
 In a lattice, any two elements must have a least upper bound and a
 greatest lower bound.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9
 */
trait Lattice[A] extends JoinSemiLattice[A] with MeetSemiLattice[A] {

  private val lattice = this ;

  /**
   Injects a compatible object into the lattice ordering. (Useful for creating implicits.)
   */ 
  override def inject[B <% A] (x : B) : Latticed[A] = new Latticed[A] {
    def partialCompare(y : A) = lattice.partialCompare(x, y)
    def join (y : A) = lattice.join(x,y)
    def meet (y : A) = lattice.meet(x,y)
  }
}

/**
 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9
 */
trait Latticed[A] extends JoinSemiLatticed[A] with MeetSemiLatticed[A]





/**
 In a bounded lattice, there is a greatest element (top) and a least element (bot).
*/
trait BoundedLattice[A] extends Lattice[A] {

  /**
   The greatest element.
   */
  def top : A ;

  /**
   The least element.
   */
  def bot : A ;

}




/**
 An UnknownLUBException is thrown when least upper bound of two elements isn't known.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 1.0
 */
case class UnknownLUBException[A](x : A, y : A) extends RuntimeException


/**
 An UnknownGLBException is thrown when greatest lower bound of two elements isn't known.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 1.0
 */
case class UnknownGLBException[A](x : A, y : A) extends RuntimeException




/**
 A flat partial order is ordered by ==.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9
 */
trait FlatOrder[A] extends PartialOrder[A] {
  override def partialCompare (x : A, y : A) : PartialOrdering = 
    if (x == y) { EQ } else { NA }
}





/**
 A standard lifting of partial ordering to maps:

 map f is weaker than map g iff for every element x in the domain of f, it is the case that f(x) isWeakerThan g(x).

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

 */
class MapPartialOrder[K,V <% PartiallyOrdered[V]] extends PartialOrder[scala.collection.immutable.Map[K,V]] {
  import scala.collection.immutable.Map._
  override def weakerThan(m1 : Map[K,V], m2 : Map[K,V]) : Boolean = {
    for ((k1,v1) <- m1) {
      (m2 get k1) match {
        case Some(v2) => if (!(v1 isWeakerThan v2)) return false
        case None => false
      }
    }
    return true 
  }
}



/**
 
 A SumOrdered type is a partially ordered type meant for modeling the
 natural partial ordering of disjoint unions of partial orders.

 When determining the order relationship, comparison first checks the tags.

 If the tags are not equal, then the comparison yields incomparable.

 If the tags are equal, then the comparison defers to the local comparison method.
 
 */
trait SumOrdered[A <: SumOrdered[A]] extends PartiallyOrdered[A] {

  /**
   Objects are comparable only if they bear the same sumTag.
   */
  def sumTag : String ;

  /**
   Compares objects with the same sumTag.
   */
  def localPartialCompare (that : A) : PartialOrdering ;

  
  def partialCompare (that : A) : PartialOrdering = {
    if (this.sumTag equals that.sumTag) {
      localPartialCompare(that)
    } else {
      NA
    }
  }
}



/**

 A TagOrdered type is ordered first by tag, and then, for objects whose tags are equal, by a local comparsion method.

 Note that a TagOrdered type is <b>totally</b> ordered.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

 */

trait TagOrdered[A <: TagOrdered[A]] extends Ordered[A] {

  /**
   Objects are first ordered on their tag.
   
   Frequently, getClass().getName() is a suitable implementation of this method.
   */
  def orderTag : String ;

  /**
   Compares object that have the same tag type.
   */
  def localCompare (a : A) : Int ;

  /**
   Returns the result of the tag comparison unless equal.

   If the tags are equal, it returns the result of localCompare.
   */
  def compare (that : A) : Int = {
    val cmp = this.orderTag compare that.orderTag
    if (cmp == 0) 
      this localCompare that
    else
      cmp
  }
}



object TotalOrder {
  def compare [A <: Ordered[C], B <: Ordered[D],C,D] (a1 : A, b1 : B) (a2 : C, b2 : D) : Int = {
    val c1 = a1 compare a2
    if (c1 != 0)
      return c1
    b1 compare b2
  }


  def compare[K <% Ordered[K]] (s1 : scala.collection.immutable.SortedSet[K]) (s2 : scala.collection.immutable.SortedSet[K]) : Int = {
    // CHECK_HERE
    // BUG/WARNING: This assumes toList returns a list ordered by key.

    for ((k1,k2) <- s1.toList zip s2.toList) {
      val c = k1 compare k2
      if (c != 0)
        return c
    }

    val csize = s1.size - s2.size
    if (csize != 0)
      return csize

    return 0
  }


  def compare[K <% Ordered[K],V <: Ordered[V]] (m1 : scala.collection.immutable.SortedMap[K,V]) (m2 : scala.collection.immutable.SortedMap[K,V]) : Int = {
    // CHECK_HERE
    // BUG/WARNING: This assumes toList returns a list ordered by key.

    for (((k1,v1),(k2,v2)) <- m1.toList zip m2.toList) {
      val ck = k1 compare k2
      if (ck != 0)
        return ck
      
      val cv = v1 compare v2
      if (cv != 0)
        return cv
    }

    // Check if one is larger than the other.
    val csize = m1.size - m2.size
    if (csize != 0)
      return csize 


    return 0
  }
  

  /**
   Casts an object into an order.
   */
  def orderIdentity[A] (a : A) : Ordered[A] = a.asInstanceOf[Ordered[A]]
}
