package org.ucombinator.languages.json ;




/**
 A JSONExp object is as an abstract syntax node for JSON-formatted data.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.1
 */
trait JSONExp extends JSONable {
  def toString(sb : StringBuilder) : Unit ;
  override def toString = {
    val sb = new StringBuilder
    toString(sb)
    sb.toString()
  }

  def toJSON() = this
}


/**
 JSONSyntax contains the types of abstract syntax nodes for JSON data.

  <b>Bug warning</b>: Proper quoting of string literal not yet implemented.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.1
 */
object JSONSyntax {
  
  /**
   Converts characters which are illegal (e.g. \n) inside JSON string literals into their corresponding escape sequences.
   */
  private def quote(string : String) : String = {
    string.replaceAll("\\\\","\\\\")
          .replaceAll("\"","\\\"")
          .replaceAll("\n","\\n")
          .replaceAll("\r","\\r")
  }

  /**
   Converts illegal characters into escape sequences and adds quotes (") around the string.
   */
  private def quotes(string : String) : String = "\"" + quote(string) + "\""

  /**
   Objects.
   */
  case class O(val map : Map[String,JSONExp]) extends JSONExp {
    def toString(sb : StringBuilder) {
      sb.append("{")
      var first = true
      for ((k,v) <- map) {
        if (!first) {
          sb.append(",\n") 
        } else {
          first = false
        }
        sb.append(quotes(k))
        sb.append(": ")
        v.toString(sb)
      }
      sb.append("}\n")
    }
  }

  /**
   Arrays.
   */
  case class A(val seq : List[JSONExp]) extends JSONExp {
    def toString(sb : StringBuilder) {
      sb.append("[") 
      var first = true
      for (el <- seq) {
        if (!first)
          sb.append(", \n")
        else
          first = false
        el.toString(sb)
      }
      sb.append("]")
    }
  }


  /**
   Integers.
  */
  case class Z(val int : BigInt) extends JSONExp {
    def toString(sb : StringBuilder) {
      sb.append(int.toString)
    }
  }

  
  /**
   Strings.
   */
  case class T(val text : String) extends JSONExp {
    def toString(sb : StringBuilder) {
      sb.append(quotes(text.toString)) 
    }
  }

  /**
   Variables.
   */
  case class S(val name : String) extends JSONExp {
    def toString(sb : StringBuilder) {
      sb.append(name)
    }
  }

  /**
   Functor application.
   */
  case class F(val fun : String, val args : List[JSONExp]) extends JSONExp {
    def toString(sb : StringBuilder) {
      sb.append(fun)
      sb.append("(")
      var first = true 
      for (a <- args) {
        if (!first)
          sb.append(", \n")
        else
          first = false
        a.toString(sb)
      }
      sb.append(")")
    }
  }

}


trait JSONable {
  def toJSON() : JSONExp
}


/**
 The JSON object provides convenience methods.
 */
object JSON {
  import JSONSyntax._


  /**
   Converts an iterable object into a JSON array.

   <b>Warning</b>: This method name will be changed.
   */
  def fromIterable(a : Iterable[JSONable]) : JSONExp = {
    A(a.toList map (_.toJSON()))
  }

  def apply[A,B](o : Iterable[(A,B)]) : JSONExp = {
    var m = scala.collection.immutable.Map[String,JSONExp]()
    for ((s,a) <- o) {
      m = m + ((s.toString(),a.asInstanceOf[JSONable].toJSON()))
    }
    O(m)
  }
}
