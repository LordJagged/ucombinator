package org.ucombinator.util ;


/**

 CPS is library of procedures useful when coding in continuation-passing style.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.1

 */

object CPS {
  
  def mapK[X,Y,Z] (f : X => (Y => Z) => Z) (l : List[X]) (k : List[Y] => Z) : Z = l match {
    case hd :: tl => 
      f (hd) (hd_ =>
        mapK (f) (tl) (tl_ => 
          k(hd_ :: tl_)))
    case List() => k(List())
  }

}
