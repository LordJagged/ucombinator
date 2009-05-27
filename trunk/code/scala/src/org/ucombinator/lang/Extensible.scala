package org.ucombinator.lang ;

/**

  An Extensible object can store arbitrary properties.

  The primary purpose of Extensibile is to allow implicits to attach local information to an object.

  For example, an abstract syntax tree node class could be made Extensible, 
  if the class author expects annotations to be added to nodes by third parties, 
  such as a static analyzer suite.

  @author <a href="http://matt.might.net/">Matthew Might</a>
  @version 1.0

 */

trait Extensible {

  /**
   When an implicit is used to extend the interface of an object, 
   it can store local information in the __properties HashMap.
   */
  lazy val __properties = new scala.collection.mutable.HashMap[Any,Any]() 
}
