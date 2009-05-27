package org.ucombinator.util ;


/**
 
 A Canonicalizer keeps track of the canonical instance of an object.

 Canonicalization is meant to work only with purely functional objects.
 
 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

 */
trait Canonicalizer[V] {

  /**
   Returns the canonical instance of value v.
   */
  def apply(v : V) : V ;
}



/**
 
 A HashCanonicalizer returns the canonical instance of an object,
 where equality is deterimed by the hashCode and equals methods.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.9

 */
trait HashCanonicalizer[V] extends Canonicalizer[V] {
  private val table = new scala.collection.mutable.HashMap[V,V]
  
  def apply(v : V) : V = {
    (table get v) match {
      case Some(v_) => { 
        v_
      }
      case None => {
        table(v) = v
        v
      }
    }
  }
}


// TODO: Ordered canonicalizer.
