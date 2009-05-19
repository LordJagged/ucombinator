/**

 An S-Expression library.

 Copyright: BSD Open Source License (see footer)

 @author <a href="http://matt.might.net/">Matthew Might</a>

 */

package org.ucombinator.languages.sexp ;

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.syntax._ 
import scala.util.parsing.input.Positional 


/**
  <p>
  S-Expressions are a generic tree-like data structure.  

  They are most commonly used to represent code and data in
  programming languages such as Scheme and Lisp.

  S-Expressions are typically encoded concretely using nested
  parentheses as symbols, e.g.:
  <pre>
    (car  
      (model     740iL)
      (color     black)
      (top-speed 160))
  </pre>
  and:
  <pre>
    (define (factorial n)
      (if (= n 0)
          1
          (* n (factorial (- n 1)))))
  </pre> 
  </p>

  <p>
  SExp is the abstract syntax for S-Expression-encoded data.
  </p>

  @author <a href="http://matt.might.net/">Matthew Might</a>
  @version 0.3
*/
trait SExp extends Positional {

  /**
   Every S-Expression has a unique serial number.
   */
  lazy val serial = SExp.allocateSerial(this)
}


/*
  @author <a href="http://matt.might.net/">Matthew Might</a>
  @version 0.3
*/
object SExp {
  private var maxSerial : Long = 0

  private val serialMap = new scala.collection.mutable.HashMap[Long,SExp]()

  private [sexp] def allocateSerial(sx : SExp) : Long = {
    var newSerial : Long = -1
    synchronized {
      newSerial = maxSerial + 1
      maxSerial = newSerial
      serialMap(newSerial) = sx
    }
    newSerial
  }

  /**
   Look up an object based in its unique serial number.
   */
  def apply(serial : Long) : SExp = serialMap(serial)
}


/**
  @author <a href="http://matt.might.net/">Matthew Might</a>
  @version 0.3
 */

object SExpSyntax {

  /** 
   S-Expression lists: <code>( <i>sx</i><sub>1</sub> ... <i>sx</i><sub>n</sub> )</code>. 
   @author <a href="http://matt.might.net/">Matthew Might</a>
  */
  case class L(var args : List[SExp]) extends SExp { 
    def apply(i : Int) : SExp = args(i)
    override def toString = "(" +(args mkString " ")+ ")"
  }

  /** 
   S-Expression smbols. 
   @author <a href="http://matt.might.net/">Matthew Might</a>
   */
  case class S(var chars : String) extends SExp {
    override def toString = chars
  }

  /**
   S-Expression primitives: Meaning is context-dependent. 
   @author <a href="http://matt.might.net/">Matthew Might</a>
   */
  case class P(var chars : String) extends SExp {
    override def toString = chars
  }

  /**
   S-Expression integers. 
   @author <a href="http://matt.might.net/">Matthew Might</a>
   */
  case class Z(var z : BigInt) extends SExp {
    override def toString = z.toString
  }

  // Arbitrary-precision decimal.
  // case class D(var lhs : String, var rhs : String) extends SExp // TODO


  /**
   S-Expression quoted text. (Strings.) 
   @author <a href="http://matt.might.net/">Matthew Might</a>
   */
  case class T(var chars : String) extends SExp {
    override def toString = chars
  }

}



// Tokens for the lexer:
private [sexp] trait STokens extends Tokens {
  case class SSymbol(val chars : String) extends Token 
  case class SInteger(val chars : String) extends Token
  // case class SDecimal(val chars : String) extends Token // TODO
  case class SText(val chars : String) extends Token
  case class SPunct(val chars : String) extends Token 
  case class SPrim(val chars : String) extends Token // #<[chars]>
  case class SImpossible extends Token {
    val chars = "IMPOSSIBLE-TOKEN!"
  }
}

import SExpSyntax._

// Lexer for S-Expressions:
private [sexp] class SLexical extends Lexical with STokens {
  import scala.util.parsing.input.CharArrayReader.EofCh
  
  def whitespace : Parser[Any] = rep(
      whitespaceChar
    | ';' ~ rep( chrExcept(EofCh, '\n') ) // Scheme-style comment.
    )

  def token : Parser[Token] = (
      ('(') ^^ { case c => SPunct(c.toString()) }
    | (')') ^^ { case c => SPunct(c.toString()) }
    | ('\'') ^^ { case c => SPunct(c.toString()) }
    | ('-' ~ rep1(digit)) ^^ { case '-' ~ chars => SInteger("-" + (chars mkString "")) }
    | ('"' ~ rep(chrExcept('"',EofCh)) ~ '"') ^^ { case '"' ~ chars ~ '"' => SText(chars mkString "") }
    | ('#' ~ '<' ~ rep(chrExcept('>')) ~ '>') ^^ { case '#' ~ '<' ~ chars ~ '>' => SPrim(chars mkString "") } 
    | (rep1(digit)) ^^ { case chars => SInteger(chars mkString "") }
    | (rep1(chrExcept(EofCh, '\r', '\n', '\t', ' ', '(', ')', '\'', ';'))) ^^
        { case chars => SSymbol((chars) mkString "") }
    | EofCh ^^^ EOF
    )
}


/**

  An SParser object parses S-Expression-formatted inputs.

  @author <a href="http://matt.might.net/">Matthew Might</a>
  @version 0.3

 */
class SParser extends TokenParsers {
  
  /**
   If true, <code>'<i>sx</i></code> is treated as <code>(quote <i>sx</i>)</code>.
   */
  var allowsQuotes = true
  //var allowsQuasiquotes = true // TODO

  type Tokens = STokens
  val lexical = new SLexical
  
  import lexical.{SSymbol,SPunct,SInteger,SText,SImpossible,SPrim}

  // keyword: Automatically turn a string into an appropriate parser.
  private implicit def keyword(chars: String): Parser[String] = chars match {
    case ("("|")"|"'") => accept(SPunct(chars)) ^^ (_.chars)
    case _ => accept(SSymbol(chars)) ^^ (_.chars)
  }
  
  /* Grammar. */

  // Start symbol:
  private def prog : Parser[List[SExp]] = phrase(exp *) ^^ { case exps => exps }

  
  // Terminals: 
  private def symbol : Parser[String] =
    elem("symbol", _.isInstanceOf[SSymbol]) ^^ (_.chars)

  private def integer : Parser[BigInt] =
    elem("integer", _.isInstanceOf[SInteger]) ^^ { case s => BigInt(s.chars) }

  private def text : Parser[String] =
    elem("text", _.isInstanceOf[SText]) ^^ { _.chars }

  private def prim : Parser[String] =
    elem("primitive", _.isInstanceOf[SPrim]) ^^ { _.chars } 


  // Non-terminals: 
  private def t : Parser[T] = positioned(text ^^ {case text => T(text)})

  private def s : Parser[S] = positioned(symbol ^^ { case s => S(s) })

  private def z : Parser[Z] = positioned(integer ^^ { case bi => Z(bi) }) 

  private def p : Parser[P] = positioned(prim ^^ { case p => P(p) })

  private def list : Parser[L] = positioned(("(" ~ (exp *) ~ ")") ^^
    { case "(" ~ sxs ~ ")" => L(sxs) })
  
  private def qexp : Parser[SExp] = 
    if (allowsQuotes) {
      positioned(("'" ~ exp) ^^
                 { case "'" ~ exp => L(List(S("quote"),L(List(exp)))) })
    } else {
      elem("impossible", _.isInstanceOf[SImpossible]) ^^ { case SImpossible() => S("Impossible-Token-Parsed!") }
    }



  private def exp : Parser[SExp] = positioned((list | qexp | z | s | t | p) ^^ { case e => e })

  // External interface:

  def parse (s : String) : List[SExp] =
    parse(new lexical.Scanner(s))


  def parse (r : lexical.Scanner) : List[SExp] = {
    prog(r) match {
      case Success(sx, _) => sx

      case Failure(msg,_) =>
       throw new Exception("parse failed: " + msg)

      case Error(msg,_) =>
       throw new Exception("parse error: " + msg)
    }
  }
}



/**
 
  A unit test object for S-Expressions.

  @author <a href="http://matt.might.net/">Matthew Might</a>
  @version 0.1
 */
object SExpTest {

  def test1() {
    val input = " (foo ( bar)\n baz);)(" ;
    val sparser = new SParser() ;
    val sexps = sparser.parse(input) ;

    val expect = "(foo (bar) baz)"
    if (sexps.head.toString != expect) {
      println("Bug in SExp when parsing " + input)
    } else {
      println("Test passed.")
    }
  }


  def main (args : String) {
    test1()
  }
}




/*

COPYRIGHT INFORMATION

Copyright (c) 2009, Matthew Might
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the U Combinator Organization nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY Matthew Might ''AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL Matthew Might BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*/
