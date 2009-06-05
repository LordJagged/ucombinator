package org.ucombinator.project.lambdo ;

import org.ucombinator.languages.{SyntaxNode,AlphaSyntaxNode} ;
import org.ucombinator.languages.sexp.{SExp,SExpSyntax,SParser} ;
import org.ucombinator.languages.json.{JSONable,JSONExp,JSONSyntax} ;


import scala.collection.immutable.{SortedMap,TreeMap} ;


/*
 
 Syntax:

 <field-name> ::= <symbol>

 <var> ::= <symbol>

 <exp> ::= <var>

        |  (lambda (<var> ...) <exp:body>)

        ; Records:
        |  (record (<field-name> <exp:value>) ...)
        |  (set-field! <exp:record> <field-name> <exp:value> <exp:body>)
        |  (get-field  <exp:record> <field-name>)

 TODO:
        | (reflect-get-field  <exp:record> <exp:field>)
        | (reflect-set-field! <exp:record> <exp:field> <exp:value> <exp:body>)
        
 
 */


/** 

 LambdoSyntax contains all of the AST data types and primitive
 (non-macro-expanding) parsers.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.3

 */

object LambdoSyntax {
  import SExpSyntax._ ;


  /* 
   These objects provide custom pattern matching on S-Expressions.

   They match constructs from the Lambdo programming language.
   */


  /**
   Matches <code>(lambda (<i>v</i><sub>1</sub> ... <i>v</i><sub><i>n</i></sub>) <i>sx</i>)</code>.
   */
  object SLambda {
    // unapply() is the inverse of apply()
    def unapply(sx : SExp) : Option[(List[S], SExp)] = sx match {
      case L(S("lambda") :: L(sxvars) :: List(sxbody)) =>
        Some(sxvars.map(_.asInstanceOf[S]), sxbody)
      case _ => None
    }
  }
  
  /**
   Matches <code>(define <i>sx</i> <i>sx'</i>)</code>.
   */
  object SDefine {
    def unapply(sx : SExp) : Option[(SExp, SExp)] = sx match {
      case L(S("define") :: formula :: List(value)) => Some(formula, value)
      case _ => None
    }
  }

  /**
   Matches <code>(if <i>sx</i> <i>sx'</i> <i>sx''</i>)</code>; or
   matches <code>(if <i>sx</i> <i>sx'</i>)</code> as 
   <code>(if <i>sx</i> <i>sx'</i> (begin))</code>.
   */
  object SIf {
    def unapply(sx : SExp) : Option[(SExp,SExp,SExp)] = sx match {
      case L(S("if") :: cond :: cons :: alt :: List()) => Some(cond,cons,alt)
      case L(S("if") :: cond :: cons :: List()) => Some(cond,cons,L(List(S("begin"))))
      case _ => None
    }
  }

  /**
   Matches <code>(cond <i>sx</i> ...)</code>.
   */
  object SCond {
    def apply(sxs : List[SExp]) = L(S("cond") :: sxs)
    def unapply(sx : SExp) : Option[List[SExp]] = sx match {
      case L(S("cond") :: clauses) => Some(clauses)
      case _ => None
    }
  }

  /**
   Matches <code>(and <i>sx</i> ...)</code>.
   */
  object SAnd {
    def apply(sxs : List[SExp]) = L(S("and") :: sxs)
    def unapply(sx : SExp) : Option[List[SExp]] = sx match {
      case L(S("and") :: conds) => Some(conds)
      case _ => None
    }
  }

  /**
   Matches <code>(or <i>sx</i> ...)</code>.
   */
  object SOr {
    def apply(sxs : List[SExp]) = L(S("or") :: sxs)
    def unapply(sx : SExp) : Option[List[SExp]] = sx match {
      case L(S("or") :: conds) => Some(conds)
      case _ => None
    }
  }

  /**
   Matches <code>(or|| <i>sx</i> ...)</code>.
   */
  object SOrPar {
    def apply(sxs : List[SExp]) = L(S("or||") :: sxs)
    def unapply(sx : SExp) : Option[List[SExp]] = sx match {
      case L(S("or||") :: conds) => Some(conds)
      case _ => None
    }
  }

  /**
   Matches <code>(and|| <i>sx</i> ...)</code>.
   */
  object SAndPar {
    def apply(sxs : List[SExp]) = L(S("and||") :: sxs)
    def unapply(sx : SExp) : Option[List[SExp]] = sx match {
      case L(S("and||") :: conds) => Some(conds)
      case _ => None
    }
  }


  /**
   Matches <code>(let ((<i>v</i> <i>sx</i>)) <i>sx'</i>)</code>.
   */
  object SLet1 {
    def unapply(sx : SExp) : Option[(S,SExp,SExp)] = sx match {
      case L(S("let") :: L(List(L(List(v, value)))) :: body :: List()) => Some(v.asInstanceOf[S], value, body)
      case _ => None
    }
  }


  /**
   Matches <code>(let ((<i>v</i><sub>1</sub> <i>sx</i><sub>1</sub>) ... (<i>v</i><sub><i>n</i></sub> <i>sx</i><sub><i>n</i></sub>)) <i>sx'</i>)</code>.
   */
  object SLet {
    def unapply(sx : SExp) : Option[(List[S], List[SExp], SExp)] = sx match {
      case L(S("let") :: L(clauses) :: body :: List()) => { 
        val namesXvalues : List[(S,SExp)] = clauses map ({case L(List(name,value)) => (name.asInstanceOf[S],value)})
        val (names,values) = List.unzip(namesXvalues)
        Some(names,values,body)
      }
      case _ => None
    }
  }


  /**
   Matches <code>(let* ((<i>v</i><sub>1</sub> <i>sx</i><sub>1</sub>) ... (<i>v</i><sub><i>n</i></sub> <i>sx</i><sub><i>n</i></sub>)) <i>sx'</i>)</code>.
   */
  object SLets {
    def unapply(sx : SExp) : Option[(List[S], List[SExp], SExp)] = sx match {
      case L(S("let*") :: L(clauses) :: body :: List()) => { 
        val namesXvalues : List[(S,SExp)] = clauses map ({case L(List(name,value)) => (name.asInstanceOf[S],value)})
        val (names,values) = List.unzip(namesXvalues)
        Some(names,values,body)
      }
      case _ => None
    }
  }


  /**
   Matches <code>(let|| ((<i>v</i><sub>1</sub> <i>sx</i><sub>1</sub>) ... (<i>v</i><sub><i>n</i></sub> <i>sx</i><sub><i>n</i></sub>)) <i>sx'</i>)</code>.   
   */
  object SLetPar {
    def unapply(sx : SExp) : Option[(List[S], List[SExp], SExp)] = sx match {
      case L(S("let||") :: L(clauses) :: body :: List()) => { 
        val namesXvalues : List[(S,SExp)] = clauses map ({case L(List(name,value)) => (name.asInstanceOf[S],value)})
        val (names,values) = List.unzip(namesXvalues)
        Some(names,values,body)
      }
      case _ => None
    }
  }


  /**
   Matches <code>(letrec ((<i>v</i><sub>1</sub> <i>sx</i><sub>1</sub>) ... (<i>v</i><sub><i>n</i></sub> <i>sx</i><sub><i>n</i></sub>)) <i>sx'</i>)</code>.   
   */
  object SLetRec {
    def unapply(sx : SExp) : Option[(List[S], List[SExp], SExp)] = sx match {
      case L(S("letrec") :: L(clauses) :: body :: List()) => { 
        val namesXvalues : List[(S,SExp)] = clauses map ({case L(List(name,value)) => (name.asInstanceOf[S],value)})
        val (names,values) = List.unzip(namesXvalues)
        Some(names,values,body)
      }
      case _ => None
    }
  }

  /**
   Matches <code>(set! <i>v</i> <i>sx</i> <i>sx</i><sup>?</sup>)</code>.
   */
  object SSet {
    def unapply(sx : SExp) : Option[(S, SExp, Option[SExp])] = sx match {
      case L(S("set!") :: v :: value :: List()) => Some(v.asInstanceOf[S], value, None)
      case L(S("set!") :: v :: value :: body :: List()) => Some(v.asInstanceOf[S], value, Some(body))
      case _ => None
    }
  }


  /**
   Matches <code>(begin <i>sx</i> ...)</code>.
   */
  object SBegin {
    def unapply(sx : SExp) : Option[List[SExp]] = sx match {
      case L(S("begin") :: cmds) => Some(cmds)
      case _ => None
    }
  }


  object SRecord {
    private def parseClause(clause : SExp) : (S,SExp) = clause match {
      case L(List(s : S, sx)) => (s,sx)
      case _ => throw new Exception("Error while parsing (record ...) field clause: " + clause)
    }

    def unapply(sx : SExp) : Option[(List[S],List[SExp])] = sx match {
      case L(S("record") :: clauses) => Some(List.unzip(clauses map parseClause))
      case _ => None
    }
  }

  object SSetField {
    def unapply(sx : SExp) : Option[(SExp,S,SExp,SExp)] = sx match {
      case L(List(S("set-field!"), sxrec, sxfield : S, sxvalue, sxbody)) => Some((sxrec,sxfield,sxvalue,sxbody))
      case _ => None
    }
  }

  object SGetField {
    def unapply(sx : SExp) : Option[(SExp,S)] = sx match {
      case L(List(S("get-field"), sxrec, sxfield : S)) => Some((sxrec,sxfield))
      case _ => None
    }
  }


  /* Terms. */

  /**
   A Term is an abstract syntax tree node.
   */
  abstract class Term extends SyntaxNode with JSONable {

    /**
     The original source of this Term, if any.
     */
    var source : SExp = null

    /**
     Sets the source of this term.
     */
    def setSource (source : SExp) : Term = {
      this.source = source
      this
    }

    /**
     An S-Expression representation of this term.
     */
    def toSExp : SExp ;

    override def toString = toSExp.toString

    def toJSON() : JSONExp = JSONSyntax.T(this.toString)
  }

  /* Denoters. */

  /**
   A Var is a bindable variable name.
   */
  case class Var(val name : String) extends Term with AlphaSyntaxNode {
    val internalName = name
    override val toString = name
    override def setSource (sx : SExp) : Var = super.setSource(sx).asInstanceOf[Var]
    override def toSExp : SExp = S(name)
  }
  
  
  private [project] implicit def varToOrdered(v : Var) : Ordered[Var] = new Ordered[Var] {
    def compare (v2 : Var) : Int = v compare v2
  }


  /*
   
   It is frequently the case that fresh variables have to be generated
   during a program transformation.

   Often times, these generate variables are bound to specific values
   in the original (or the transformed) program.

   These special kinds of variables remember the context and the
   reason for which they were generated.

   These links make it easier to project results of a static analysis
   on a transformed program back onto the original program.

   */

  /**
   An ExpVar variable gets bound to the result of another expression.

   This is useful during flattening transformations.
   */
  case class ExpVar (val exp : Exp) extends Var("$=$" + exp.label) {
  }

  /**
   A ContVar variable is the current-continuation variable of a specific direct-style lambda expression.

   This is useful during CPS transformation.
   */
  case class ContVar (val lam : Lambda) extends Var("$k$" + lam.label) {
  }

  /**
   A RetVar variable gets bound to the result of a direct-style application expression.

   This is useful during CPS transformation.
   */
  case class RetVar (val app : Exp) extends Var("$rv$" + app.label) {
  }


  /* Definitions. */

  /**
   A Def object represents the equation of a variable with some expression.
   */
  abstract class Def(val name : Var) extends Term {
    def rhs : Exp ;
    def toSExp = L(List(S("define"), S(name.name), rhs.toSExp))
    override def setSource (sx : SExp) : Def = super.setSource(sx).asInstanceOf[Def]
  }

  /**
   A VarDef object encodes the definition of a variable.
   */
  case class VarDef (n : Var, value : Exp) extends Def(n) {
    def rhs : Exp = value
  }

  /**
   A FunDef object implicitly encodes the definition of a variable to a function.
   */
  case class FunDef (n : Var, args : List[Var], body : Exp) extends Def(n) {
    def rhs : Exp = Lambda(args,body)
  }

  /**
   An ImpDef object is an implicif definiton: a top-level expression is bound to the variable <code>last</code>.
   */

  case class ImpDef (value : Exp) extends Def(Var("last")) {
    def rhs : Exp = value
  }





  /* Expressions */

  /**
   The evaluation of a trivial expression is guaranteed to terminate,
   mutates no existing resource, and performs no I/O.
   */
  trait TrivialExp extends Exp

  /**
   An Exp object represents an evaluable term.
   */
  type FreeSet = scala.collection.immutable.Set[Var]

  abstract class Exp extends Term {
    override def setSource (sx : SExp) : Exp = super.setSource(sx).asInstanceOf[Exp]

    def freeVars : FreeSet = throw new Exception("freeVars() not yet implemented in " + this.getClass().getName())
  }
  
  private def freeVarsIn(exps : List[Exp]) : FreeSet = 
    (exps.map(_.freeVars).foldRight (scala.collection.immutable.Set[Var]()) (_ ++ _))

  // Core:

  /**
   A Lambda expression, upon evaluation, becomes a function.
   */
  case class Lambda (val params : List[Var], val body : Exp) extends TrivialExp {
    def toSExp = L(List(S("lambda"), L(params map (v => S(v.name))), body.toSExp))
    
    override lazy val freeVars : FreeSet = body.freeVars -- params
  }

  /**
   A Ref expression evaluates to the current value of the variable.
   */
  case class Ref (val v : Var) extends TrivialExp {
    def toSExp = S(v.name)

    override lazy val freeVars : FreeSet = scala.collection.immutable.TreeSet[Var]() + v
  }

  /**
   An App expression represents the application af a function to a sequence of arguments.
   */
  case class App (f : Exp, args : List[Exp]) extends Exp {
    def toSExp = L(f.toSExp :: (args map (_.toSExp)))

    override lazy val freeVars : FreeSet = f.freeVars ++ freeVarsIn(args)
  }

  /**
   An OrPar expression represents a disjunctive formula whose operands may be evaluated in parallel.
   */
  case class OrPar(conds : List[Exp]) extends Exp {
    def toSExp = L(S("or||") :: (conds map (_.toSExp)))

    override lazy val freeVars : FreeSet = freeVarsIn(conds)
  }

  /**
   An AndPar expression represents a conjunctive formula whose operands may be evaluated in parallel.
   */
  case class AndPar(conds : List[Exp]) extends Exp {
    def toSExp = L(S("and||") :: (conds map (_.toSExp)))

    override lazy val freeVars : FreeSet = freeVarsIn(conds)
  }

  /**
   A LetPar expression represents a let expression whose clauses may be evaluated in parallel.
   */
  case class LetPar(names : List[Var], values : List[Exp], body : Exp) extends Exp {
    def toSExp = L(List(S("let||"), L((names zip values) map { case (n,v) => L(List(S(n.name),v.toSExp)) }), body.toSExp))
  }


  // Sugar:

  /**
   An If expression represents a conditional.
   */
  case class If (cond : Exp, ifTrue : Exp, ifFalse : Exp) extends Exp {
    def toSExp = L(List(S("if"), cond.toSExp, ifTrue.toSExp, ifFalse.toSExp))
    override lazy val freeVars : FreeSet = freeVarsIn(List(cond,ifTrue,ifFalse))
  }

  /**
   A Let1 expression binds an expression to a variable, and then returns the value of the body.
   */
  case class Let1(v : Var, value : Exp, body : Exp) extends Exp {
    def toSExp = L(List(S("let"), L(List(L(List(S(v.name), value.toSExp)))), body.toSExp))
    override lazy val freeVars : FreeSet = value.freeVars ++ (body.freeVars - v)
  }

  /**
   A LetRec expression permits mutually recursive lambdas.
   */
  case class LetRec(names : List[Var], values : List[Lambda], body : Exp) extends Exp {
    def toSExp = L(List(S("letrec"), L((names zip values) map { case (n,v) => L(List(S(n.name),v.toSExp)) }), body.toSExp))

    override lazy val freeVars : FreeSet = (freeVarsIn(values) ++ body.freeVars) -- names
  }

  /**
   A Set expression mutates the value of a variable before proceeding.
   */
  case class Set(v : Var, value : Exp, body : Exp) extends Exp {
    def toSExp = L(List(S("set"), S(v.name), value.toSExp, body.toSExp))
    
    override lazy val freeVars : FreeSet = (body.freeVars ++ value.freeVars) + v
  }

  /**
   A Seq expression evaluates a sequence of expression, 
   discarding all values except the value of the last expression.
   */
  case class Seq(exps : List[Exp]) extends Exp {
    def toSExp = L(S("begin") :: (exps map (_.toSExp)))

    override lazy val freeVars : FreeSet = freeVarsIn(exps) 
  }

  // Real sugar:

  /**
   A Let expression is desugared into the immediate application of a Lambda term:

   <p>
    <code>(let ((<i>v</i> <i>e</i>) ...) <i>b</i>)</code> =>
    <code>((lambda (<i>v</i> ...) <i>b</i>) <i>e</i> ...)</code>
   </p>
   */
  object Let {
    def apply(names : List[Var], exps : List[Exp], body : Exp) : Exp = 
      App(Lambda(names,body), exps)
  }
  
  /**
   An And expression is desugared into a conditional:
   <ul>

    <li><code>(and <i>cond</i> <i>conds</i> ...)</code> =>
        <code>(if <i>cond</i> (and <i>conds</i> ...) #f)</code>.</li>

    <li><code>(and cond)</code> => <code><i>cond</i></code></li>

    <li><code>(and)</code> => <code>#t</code></li>

   </ul>
    */
  object And {
    def apply(conds : List[Exp]) : Exp = conds match {
      case List(last) => last
      case List() => BoolLit(true)
      case cond :: conds => If(cond,And(conds),BoolLit(false))
    }
  }

  /**
   An Or expression is desugared into a conditional and a let:
   <ul>

    <li><code>(or <i>cond</i> <i>conds</i> ...)</code> =>
        <code>(let ((<i>v'</i> cond)) (if <i>v'</i> <i>v'</i> (or <i>conds</i> ...))</code>.</li>

    <li><code>(or cond)</code> => <code><i>cond</i></code></li>

    <li><code>(or)</code> => <code>#f</code></li>

   </ul>
   */
  object Or {
    def apply(conds : List[Exp]) : Exp = conds match {
      case List(last) => last
      case List() => BoolLit(false)
      case cond :: conds => {
        val v = ExpVar(cond)
        val r = Ref(v)
        Let1(v,cond,If(r,r,Or(conds)))
      }
    }
  }

  /**
   A Lets expression desugars into nested Let1 expressions.
   */
  object Lets {
    def apply(names : List[Var], exps : List[Exp], body : Exp) : Exp = 
      (names,exps) match {
        case (name :: names, exp :: exps) => Let1(name,exp,Lets(names,exps,body))
        case (List(),List()) => body
      }
  }

  /**
   A Sets expression desugars into nested Set expressions.
   */
  object Sets {
    def apply(names : List[Var], exps : List[Exp], body : Exp) : Exp = 
      (names,exps) match {
        case (name :: names, exp :: exps) => Set(name,exp,Sets(names,exps,body))
        case (List(),List()) => body
      }
  }



  /*
   Object-related expressions.
   */

  type Field = Var

  case class Record(fields : List[Field], values : List[Exp]) extends Exp {
    private def sclause (fe : (Field,Exp)) : SExp = L(List(fe._1.toSExp, fe._2.toSExp))

    def toSExp = L(S("record") :: (fields.zip(values) map sclause))
    override def freeVars = freeVarsIn(values)
  }

  case class SetField(rec : Exp, field : Field, value : Exp, body : Exp) extends Exp {
    def toSExp = L(List(S("set-field!"), rec.toSExp, field.toSExp, value.toSExp, body.toSExp))
    override def freeVars = rec.freeVars ++ value.freeVars ++ body.freeVars
  }

  case class GetField(rec : Exp, field : Field) extends Exp {
    def toSExp = L(List(S("get-field"), rec.toSExp, field.toSExp))
    override def freeVars = rec.freeVars
  }


  /**
   A LitExp object represents literal constant expression.
   */
  trait LitExp extends TrivialExp {
    override val freeVars = scala.collection.immutable.Set[Var]()
  }

  /**
   A VoidLit expression evaluates to the void value.
   */
  case class VoidLit extends Exp with LitExp {
    def toSExp = L(List(S("begin")))
  }
  /**
   A TextLit expression evaluates to a string constant.
   */
  case class TextLit(chars : String) extends Exp with LitExp {
    def toSExp = T(chars)
  }
  /**
   A BoolLit expression encodes a Boolean constant: true or false.
   */
  case class BoolLit(value : Boolean) extends Exp with LitExp {
    def toSExp = S(if (value) { "#t" } else { "#f" })
  }
  /**
   An IntLit expression encodes an integer constant.
   */
  case class IntLit (z : BigInt) extends Exp with LitExp {
    def toSExp = Z(z)
  }
  /**
   A NilLit expression evaluates to the nil value.
   */
  case class NilLit() extends Exp with LitExp {
    def toSExp = L(List())
  }

  /* Primitives expressions. */

  /**
   A PrimOp expression represents a literal procedure.
   */
  abstract class PrimOp extends Exp {
    def p : String

    override val freeVars : FreeSet = scala.collection.immutable.Set[Var]()
  }
  /**
   An EPrimOp is a side-effecting primitive.
   */
  case class EPrimOp(val p : String) extends PrimOp {
    def toSExp : SExp = S(p)
  }
  /**
   A PPrimOp is a purely functional primitive.
   */
  case class PPrimOp(val p : String) extends PrimOp {
    def toSExp : SExp = S(p)
  }
  /**
   A UPrimOp behaves like its embedded primop, 
   but it may not perform any safety checks on its argument or its result.
   */
  case class UPrimOp(op : PrimOp) extends PrimOp {
    // Unsafe primop.
    def toSExp : SExp = S("##" + op.toSExp.toString)
    def p = "##" + op.toSExp.toString
  }

  /**
   After evaluation in direct-style, the result should be promoted to a CPS object.
   */
  case class CPS(exp : Exp) extends Exp {
    override def toSExp = L(List(S("cps"), exp.toSExp))
  }


  // Global syntax-related objects:
  private [lambdo] object SymbolTable {
    private var current = 0
    private def next() = {
      current += 1
      current
    }

    def fresh() = "$" + next()
  }
  
  /**
   Converts a S-Expression symbol into a Var.
   */
  def parseVar (sx : SExp) : Var = (sx match {
    case S(name) => Var(name)
  }).setSource(sx)


  /**
   Converts an S-Expression into a Def.
   */
  def parseDef (sx : SExp) : Def = (sx match {
    case SDefine(name : S, value) =>
      VarDef(Var(name.chars), parseExp(value))

    case SDefine(L((f : S) :: args), body) =>
      FunDef(Var(f.chars), args map parseVar, parseExp(body))
      
    case sx => ImpDef(parseExp(sx))
  }).setSource(sx)


  /**
   Handles implementation-specific primitives.
   */
  def parseSpecialPrimitive (sx : SExp) = sx.asInstanceOf[P].chars.split(" ") match {
    case _ => throw new Exception("unfinished")
  }


  /**
   Converts an S-Expression into an Exp.
   */
  def parseExp (sx : SExp) : Exp = (sx match {
    case S(p @ ("+" | "-" | "/" | "*" | "=" | "<" | "<=" | ">=" | ">" | "gcd" | "modulo" | "quotient" | "random-byte" | "not" | "random-range" | "odd?" | "even?")) => PPrimOp(p)
    case S(p @ ("display" | "newline")) => EPrimOp(p)
    case S("#f") => BoolLit(false)
    case S("#t") => BoolLit(true)
    case Z(z) => IntLit(z)
    case T(s) => TextLit(s)
    case S(v) => Ref(Var(v))
    case P(p) => parseSpecialPrimitive(sx)
    
    case SIf(cond, cons, alt) => 
      If(parseExp(cond), parseExp(cons), parseExp(alt))
    case SAnd(conds) => 
      And(conds map parseExp)
    case SOrPar(conds) => 
      OrPar(conds map parseExp)
    case SAndPar(conds) => 
      AndPar(conds map parseExp)
    case SOr(cond :: conds) =>
      If(parseExp(cond),BoolLit(true),parseExp(SOr(conds)))
    case SOr(List()) =>
      BoolLit(false)
    case SLambda(names, body) =>
      Lambda(names map parseVar, parseExp(body))
    case SCond(L(List(S("else"),value)) :: List()) =>
      parseExp(value)
    case SCond(L(List(cond,value)) :: clauses) =>
      If (parseExp(cond), parseExp(value), parseExp (SCond(clauses)))
    case SCond(L(List(cond)) :: clauses) => {
      val fv = SymbolTable.fresh
      val v = Var(fv)
      val r = Ref(v)
      Let1(v,parseExp(cond),If(r,r,parseExp(SCond(clauses))))
    }
    case SCond(List()) =>
      VoidLit()
    case SLetRec(names, values, body) =>
      LetRec(names map parseVar,
             values map (((x : Exp) => x.asInstanceOf[Lambda]) compose parseExp),
             parseExp(body))
    case SLetPar(names, values, body) => 
      LetPar(names map parseVar,
             values map parseExp,
             parseExp(body))
    case SLets(names,values,body) => {
      def parse (names : List[S],values : List[SExp],body : SExp) : Exp = 
        if (names.isEmpty)
          parseExp(body)
        else
          Let1(parseVar(names.head), parseExp(values.head), parse (names.tail,values.tail,body))
      parse (names,values,body)
    }
    case SLet1(name, value, body) =>
      Let1(parseVar(name), parseExp(value), parseExp(body))
    case SLet(names,values,body) => 
      App(Lambda(names map parseVar,parseExp(body)), values map parseExp)
    case SSet(name, value, Some(body)) =>
      Set(parseVar(name), parseExp(value), parseExp(body))
    case SSet(name, value, None) =>
      Set(parseVar(name), parseExp(value), VoidLit())
    case SBegin(exps) =>
      Seq(exps map parseExp)

    case SRecord(sxfields,sxexps) => 
      Record(sxfields map parseVar, sxexps map parseExp)
    case SSetField(sxrec,sxfield,sxvalue,sxbody) =>
      SetField(parseExp(sxrec),parseVar(sxfield),parseExp(sxvalue),parseExp(sxbody))
    case SGetField(sxrec,sxfield) =>
      GetField(parseExp(sxrec),parseVar(sxfield))

    
    case L(S("let") :: args) => throw new Exception("Compiler bug; could not properly parse: " + sx)

    case L(f :: args) => App(parseExp(f), args map parseExp)
    case L(List()) => NilLit()
  }).setSource(sx)
}



/**
 ConcreteCommon contains structures and methods common to concrete interpreters.
 */
object ConcreteCommon {
  import LambdoSyntax._
  import SExpSyntax._

  /**
   Concrete interpreters frequently equate run-time values and S-Expressions.
   */
  type Value = SExp 

  /**
   An environment maps from from a variable to a value cell.
   */
  type Env = scala.collection.immutable.Map[Var, Cell]


  abstract class Proc extends SExp
  case class Prim(p : String) extends Proc
  case class Closure(lam : Lambda, env : Env) extends Proc

  case object True extends SExp
  case object False extends SExp
  case object Unit extends SExp

  class RecordVal extends SExp {
    val fields = scala.collection.mutable.HashMap[Field,Value]()
    override def toString = fields.toString
  }
  object RecordVal {
    def apply(map : Map[String,Value]) : RecordVal = {
      val objVal = new RecordVal
      for ((s,v) <- map) {
        objVal.fields(Var(s)) = v
      }
      objVal
    }
  }


  /**
   A cell contains a (mutable) value.
   */
  class Cell(var value : Value)


  /**
   Primitives operate on values and return values.
   */
  def primEval (p : Prim, vals : List[Value]) : Value = (p,vals) match {
    case (Prim("display"),args) => {
      // TODO: Make this do the right thing.
      print(args)
      Unit
    }
    case (Prim("newline"),args) => {
      println()
      Unit
    }
    case (Prim("gcd"),List(Z(a), Z(b))) => Z(a gcd b)
    case (Prim("modulo"),List(Z(a), Z(b))) => Z(a mod b)
    case (Prim("quotient"),List(Z(a), Z(b))) => Z(a / b)
    case (Prim("random-byte"),args) => Z((Math.random * 256).asInstanceOf[Int])
    case (Prim("random-range"),List(Z(lo),Z(hi))) =>
      Z((BigDecimal(hi-lo) * BigDecimal(Math.random) + BigDecimal(lo)).toBigInt)
    case (Prim("not"),List(b)) if b != False => False
    case (Prim("not"),List(False)) => True
    case (Prim("+"),List(Z(a), Z(b))) => Z(a + b)
    case (Prim("-"),List(Z(a), Z(b))) => Z(a - b)
    case (Prim("*"),List(Z(a), Z(b))) => Z(a * b)
    case (Prim("/"),List(Z(a), Z(b))) => Z(a / b)
    case (Prim("="),List(Z(a), Z(b))) => if (a == b) True else False
    case (Prim("<="),List(Z(a), Z(b))) => if (a <= b) True else False
    case (Prim(">="),List(Z(a), Z(b))) => if (a <= b) True else False
    case (Prim("<"),List(Z(a), Z(b))) => if (a < b) True else False
    case (Prim(">"),List(Z(a), Z(b))) => if (a > b) True else False
  }
}



/**
 A denotational interpreter for Lambdo.

 Parallel constructs are not currently supported.
 */
class LambdoInterpreter {
  import SExpSyntax._
  import LambdoSyntax._
  import ConcreteCommon._

  /**
   Allocate a new cell for a value.
   */
  private def cell (value : Value) : Cell = new Cell(value)

  /* Environments. */
  private val emptyEnv : Env = scala.collection.immutable.TreeMap[Var,Cell]()
  private val globalEnv = scala.collection.mutable.HashMap[Var,Value]()
  
  /** 
   Looks up a variable in an environment, but falls back on the global
   environment.
   */
  private def lookup (e : Env) (v : Var) : Value = (e get v) match {
    case Some(cell) => cell.value
    case None => (globalEnv get v) match {
      case Some(value) => value
      case None => throw new Exception("Not in scope: " + v)
    }
  }

  /** Set a variable's value in an environment if it exists, and
  set it in the global environment if not. */
  private def set (e : Env) (v : Var) (value : Value) = (e get v) match {
    case Some(cell) => cell.value = value
    case None => globalEnv(v) = value
  }

  /**
   Enters a definition into the interpreter.
  */
  def process (d : Def) : Value = {
    val res = d match {
      case VarDef(name, value) =>  eval(value,emptyEnv)
      case FunDef(name, args, body) => eval(Lambda(args,body),emptyEnv)
      case ImpDef(value) => eval(value,emptyEnv)
    }
    globalEnv(d.name) = res
    res
  }


  /**
   Evaluates an expression in the context of the current environment.
   */
  def eval(exp : Exp, env : Env) : Value = {
    exp match {

      // Literals:
      case NilLit() => L(List())
      case VoidLit() => Unit

      case TextLit(chars) => T(chars)
      case BoolLit(true) => True
      case BoolLit(false) => False
      case IntLit(z) => Z(z)

      case PPrimOp(p) => Prim(p)
      case EPrimOp(p) => Prim(p)

      // Core:
      case Ref(name) => lookup (env) (name)

      case lam @ Lambda(args, body) => Closure(lam, env)

      case App(f, args) => { 
        val proc = eval(f,env)

        val vals : List[Value] = args map (eval(_,env))

        (proc,vals) match {
          case (Closure(Lambda(vars,body), env2),_) =>
            eval(body, env2 ++ (vars zip (vals map (cell _))))

          case (p : Prim,_) => ConcreteCommon.primEval(p,vals)
        }
      }

      
      // Sugar:
      case If(cond,cons,alt) =>
        if (eval(cond,env) != False)
          { eval(cons,env) }
        else
          { eval(alt,env) }

      case LetRec(names, funs, body) => {
        val cells = funs map ((_ : Lambda) => cell(null))
        val namesXcells = names zip cells
        val env2 = env ++ namesXcells
        val vals = funs map (eval(_,env2))

        for ((c,value) <- cells zip vals) {
          c.value = value
        }

        eval(body,env2)
      }

      case Let1(name,value,body) => 
        eval(body, env(name) = cell(eval(value,env)))

      case Set(name,value,body) => {
        set (env) (name) (eval(value,env))
        eval(body,env)
      }
      
      case Seq(List()) => Unit
      case Seq(List(exp)) => eval(exp,env)
      case Seq(exp :: rest) => {
        eval(exp,env)
        eval(Seq(rest),env)
      }
    }
  }
}




class LambdoMachine  {

  import SExpSyntax._
  import ConcreteCommon._
  import LambdoSyntax._


  /* Environments. */
  private val emptyEnv : Env = scala.collection.immutable.TreeMap[Var,Cell]()
  private val globalEnv = scala.collection.mutable.HashMap[Var,Value]()

  /**
   Looks up a variable in an environment, but falls back on the global
   environment.  
   */
  private def lookup (e : Env) (v : Var) : Value = (e get v) match {
    case Some(cell) => cell.value
    case None => (globalEnv get v) match {
      case Some(value) => value
      case None => throw new Exception("Not in scope: " + v)
    }
  }

  /**
   Set a variable's value in an environment if it exists, and
   set it in the global environment if not.
   */
  private def set (e : Env) (v : Var) (value : Value) = (e get v) match {
    case Some(cell) => cell.value = value
    case None => globalEnv(v) = value
  }
 
  /**
   Process a sequence of definitions, and add their effects to the
   global environment.
   */
  def process (defs : List[Def]) : Unit = defs match {
    case List() => Unit
    case d1 :: tail => eval (d1.rhs, emptyEnv) (values => {
      set (emptyEnv) (d1.name) (values.head)
      println(values.head)
      println()
      if (tail isEmpty) {
        ThreadPool.isMainThreadRunning = false
      } else {
        process (tail)
      }
    })
  }

  /**
   Evaluate an expression under an environment, returning the result
   by calling the current continuation.
   */
  def eval (exp : Exp, env : Env) (k : List[Value] => Unit) {
    var start = Eval(exp,env,KontPrim((), k))
    start.run()
  }


  private abstract class Kont
  private case class KontSet(v : Var, env : Env, body : Exp, kont : Kont) extends Kont
  private case class KontBind(v : Var, env : Env, body : Exp, kont : Kont) extends Kont
  private case class KontIf(ifTrue : Exp, ifFalse : Exp, env : Env, kont : Kont) extends Kont
  private case class KontSeq(exps : List[Exp], env : Env, kont : Kont) extends Kont
  private case class KontArgs(vals : List[Value], args : List[Exp], env : Env, kont : Kont) extends Kont
  private case class KontApp(kont : Kont) extends Kont
  private case class KontObj(fields : List[Field], kont : Kont) extends Kont
  private case class KontGetField(field : Field, kont : Kont) extends Kont
  private case class KontSetField(field : Field, env : Env, body : Exp, kont : Kont) extends Kont
  private case class KontPrim(scalaCompilerBugWorkaround : Unit, val k : List[Value] => Unit) extends Kont
  private case class KontHalt() extends Kont


  private sealed abstract class State {
    def next(context : Context) : State ;
    def isFinal : Boolean ;


    def run() : State = run (new Context(null))

    def run(context : Context) : State = {
      var cur = this
      while (!cur.isFinal && !context.completed) {
        cur = cur.next(context)
      }
      cur
    }
  }

  private case class Eval(val exp : Exp, env : Env, kont : Kont) extends State {
    val isFinal = false
    def next(context : Context) : State = exp match {
      case VoidLit() => AppKont(kont, List(Unit))
      case IntLit(z) => AppKont(kont, List(Z(z)))
      case TextLit(s) => AppKont(kont, List(T(s)))
      case BoolLit(true) => AppKont(kont, List(True))      
      case BoolLit(false) => AppKont(kont, List(False))
      case PPrimOp(p) => AppKont(kont, List(Prim(p)))
      case EPrimOp(p) => AppKont(kont, List(Prim(p)))
      case Ref(v) => AppKont(kont, List(lookup (env) (v)))
      case lam @ Lambda(args,body) => AppKont(kont, List(Closure(lam,env)))

      case Seq(exps) => AppKont(KontSeq(exps,env,kont),List())

      case Record(fields,e :: etail) => Eval(e,env,KontArgs(List(),etail,env,KontObj(fields,kont)))
      case GetField(exp,field) => Eval(exp,env,KontGetField(field,kont))
      case SetField(obj,field,value,body) => Eval(obj,env,KontArgs(List(),List(value),env,KontSetField(field,env,body,kont)))
      
      case If(cond,ifTrue,ifFalse) => Eval(cond,env,KontIf(ifTrue,ifFalse,env,kont))
      case Let1(v,e,body) => Eval(e,env,KontBind(v,env,body,kont))
      case Set(v,e,body) => Eval(e,env,KontSet(v,env,body,kont))
      case App(f, args) => Eval(f,env,KontArgs(List(),args,env,KontApp(kont)))

      case AndPar(List()) => AppKont(kont,List(True))

      case AndPar(exps) => {
        val sema = new Semaphore(exps.length)
        val ctxt = new Context(context)

        var result : Value = null

        ctxt.continuation = () => {
          AppKont(kont,List(result)).run(context)
        }

        for (e <- exps) {
          ThreadPool.spawn (e,env,ctxt) ((rv,ctxt) => {
            if (!ctxt.completed) {
              if (rv == False) {
                result = False
                ctxt.complete()
              } 

              if (sema.dec() == 0) {
                result = rv
                ctxt.complete()
              }
            }
          })
        }

        SuspendedState
      }
      
      case _ => throw new Exception("Not handled yet: " + exp)
    }
  }

  private case class AppProc(proc : Proc, vals : List[Value], kont : Kont) extends State {
    val isFinal = false
    def next(context : Context) : State = proc match {
      case Closure(Lambda(vars,body),env) => {
        val cells = vals map (new Cell(_))
        val varsXcells = vars zip cells
        val env_ = env ++ varsXcells
        Eval(body, env_, kont)
      }
      case p : Prim => AppKont(kont,List(ConcreteCommon.primEval(p,vals)))
    }
  }

  private case class AppKont(kont : Kont, retvals : List[Value]) extends State {
    lazy val isFinal = kont.isInstanceOf[KontHalt]
    
    def next(context : Context) : State = kont match {
      case KontArgs(vals,exp :: tail,env,kont) => 
        Eval(exp, env, KontArgs(retvals.head :: vals, tail, env, kont))
      case KontArgs(vals,List(),env,kont) => 
        AppKont(kont, (retvals.head :: vals) reverse)
      case KontSeq(List(),env,kont) =>
        AppKont(kont,List(Unit))
      case KontSeq(List(exp),env,kont) =>
        Eval(exp,env,kont)
      case KontSeq(exp :: rest,env,kont) =>
        Eval(exp,env,KontSeq(rest,env,kont))
      case KontIf(ifTrue,ifFalse,env,kont) =>
        if (retvals.head != False) {
          Eval(ifTrue,env,kont)
        } else {
          Eval(ifFalse,env,kont)
        }
      case KontBind(v,env,exp,kont) =>
        Eval(exp, env + ((v,new Cell(retvals.head))), kont)
      case KontSet(v,env,exp,kont) => {
        set (env) (v) (retvals.head)
        Eval(exp, env, kont)
      }
      case KontApp(kont) =>
        AppProc(retvals.head.asInstanceOf[Proc], retvals.tail, kont)
      case KontObj(fields,kont) => {
        val rec = new RecordVal 
        for ((f,v) <- fields zip retvals) {
          rec.fields(f) = v
        }
        AppKont(kont,List(rec))
      }
      case KontGetField(field,kont) => {
        AppKont(kont,List(retvals.head.asInstanceOf[RecordVal].fields(field)))
      }
      case KontSetField(field,env,body,kont) => {
        val rec = retvals.head.asInstanceOf[RecordVal]
        val value = retvals(1)
        rec.fields(field) = value
        Eval(body,env,kont)
      }
      case KontPrim((),k) =>
        { k(retvals) ; SuspendedState }
      case _ => throw new Exception("Unknown kont: " + kont)
    }
  }

  private case object SuspendedState extends State {
    val isFinal = true
    def next(context : Context) : State = {
      throw new Exception("Can't run from final state.")
    }
  }






  private [lambdo] class Context(parent : Context) {

    @volatile private var completed_ = false
    var children : List[Context] = List()

    var continuation : () => Unit = null

    if (parent != null) {
      parent synchronized {
        parent.children = this :: children
        if (parent.completed)
          completed_ = true
      }
    }

    def completed = completed_
    def complete() {
      synchronized {
        completed_ = true
      }
      for (child <- children) {
        // Abandon all children processes too.
        child.abort()
      }
      var cont : () => Unit = null
      synchronized {
        if (continuation != null) {
          cont = continuation
          continuation = null
        }
      }
      if (cont != null)
        cont()
    }


    def abort() {
      synchronized {
        completed_ = true
      }
      for (child <- children) {
        child.abort()
      }
    }

    
  }

  private case class ContextCompletedException extends Exception
 
   
  /**
   The TheadPool keeps a pool of worker threads available for tasks.
   */
  private [lambdo] object ThreadPool {

    var isMainThreadRunning = true

    private val numThreads = 4

    private var numTasks = 0

    private def incTasks() {
      synchronized {
        numTasks += 1
      }
    }

    private def decTasks() {
      synchronized {
        numTasks -= 1
        if (numTasks == 0)
          notify()
      }
    }

    def waitForInactivity() {
      synchronized {
        while (numTasks > 0) {
          wait()
        }
      }
    }

    class Task(val exp : Exp, val env : Env, val context : Context, val handle : (Value,Context) => Unit)

    private val queue = new java.util.concurrent.ArrayBlockingQueue[Task](1024)

    private val threads : List[Thread] = 
      for (i <- List.range(0,numThreads)) yield {
        new Thread(new Evaluator)
      }

    for (t <- threads) {
      t.start()
    }

    def stop() {
      for (t <- threads) {
        t.interrupt()
      }
    }

    class Evaluator extends Runnable {
      def run () {
        while (true)  {
          var task : Task = null
          try {
            task = queue.take() 
          } catch {
            case ex : InterruptedException => {
              if (numTasks == 0)
                return
              else
                throw new Exception("Attempting to bail with work remaining; numTasks = " + numTasks)
            }
          }
          if (task != null) {
            try {
              val state = Eval(task.exp, task.env, KontPrim((),values => {
                val rv = values.head
                task.handle(rv, task.context)
              }))
              state.run(task.context)
            } catch {
              case ContextCompletedException() => () // This context already found an answer.
                case e => { 
                  println("error in spawned thread while evaluating:\n" + task.exp)
                  e.printStackTrace()
                }
            }
            decTasks()
          }
        }
      }
    }


    def spawn(exp : Exp, env : Env, context : Context) (handle : (Value,Context) => Unit) {
      incTasks() 
      queue.add(new Task(exp,env,context,handle))
    }
  }

  /**
   A Semaphore counts down from an initial value in a thread-safe fashion.
   */
  private [lambdo] class Semaphore(numTasks : Int) {
    @volatile private var remaining = numTasks

    def dec () : Int = {
      var r : Int = 0
      synchronized {
        remaining -= 1
        r = remaining
      }
      r
    }
  }


  
}










object Lambdo {

  /* Options. */
  
  private var files : List[String] = List()

  /**
   There are two complete interpreters available--one written in an
   operational style, and one written in a denotational style. 
   
   The denotational interpreter does not support parallelism constructs.
  */
  private sealed abstract class EngineMode
  private case object ENGINE_OPERATIONAL extends EngineMode
  private case object ENGINE_DENOTATIONAL extends EngineMode
  private var engineMode : EngineMode = ENGINE_OPERATIONAL ;


  // TODO: Allow plug-ins to define new Actions.
  private abstract class Action
  /**
   Eliminate all top-level define statements and convert the program to a single expression.
   */
  private case object UNDEFINE extends Action 
  private case object CPSCONVERT extends Action
  private case object ANORMALIZE extends Action
  /**
   Dump the source code in its current form.
   */
  private case object DUMP extends Action
  /**
   Execute the program in its current form.
   */
  private case object EXECUTE extends Action
  private var actions : List[Action] = List(EXECUTE) ;


  private def parseOptions (args : List[String]) : Unit = args match {
    case "--engine" :: "operational" :: rest => { engineMode = ENGINE_OPERATIONAL ; parseOptions(rest) }
    case "--engine" :: "denotational" :: rest => { engineMode = ENGINE_DENOTATIONAL ; parseOptions(rest) }
    case file :: rest => { files = file :: files ; parseOptions(rest) }
    case Nil => { files = files reverse }
  }


  /* Verbose debugging output. */
  private var verboseMode = false

  private [lambdo] def verbose(s : String) {
    if (verboseMode) {
      print(s)
    }
  }

  private [lambdo] def verboseln(s : String) {
    verbose(s + "\n")
  }


  def parseString (source : String) : List[LambdoSyntax.Def] = {
    val sparser = new SParser
    val sxs : List[SExp] = sparser.parse(source)
    var defs : List[LambdoSyntax.Def] = sxs map LambdoSyntax.parseDef
    defs
  }

  def parseFile (file : java.io.File) : List[LambdoSyntax.Def] = {
    val source = scala.io.Source.fromFile(file) mkString ""
    parseString(source)
  }

  def parseFile (file : String) : List[LambdoSyntax.Def] = {
    parseFile(new java.io.File(file))
  }


  def main (args : Array[String]) {
    parseOptions (args toList)

    verboseln("options parsed...")

    var input : String = "" 

    // Read the input files:
    if (files isEmpty) {
      verboseln("accepting input on stdin...")
      input = (scala.io.Source.fromInputStream(System.in)) mkString ""
      verboseln("accepted input on stdin...")
    } else {
      verboseln("reading input files: " + files + "...")
      input = (for (f <- files) yield {
        (scala.io.Source.fromFile(f)) mkString ""
      }) mkString "\n\n"
      verboseln("read input files...")
    }

    verboseln("input:\n" + input)

    // Read the standard lib:
    /*
    val stdlib : String = (scala.io.Source.fromFile("lib/stdlib.scm")) mkString ""
    */

    //val source = stdlib + "\n" + input
    val source = input

    // Parse the input:
    val sparser = new SParser
    val sxs : List[SExp] = sparser.parse(source)
    var defs : List[LambdoSyntax.Def] = sxs map LambdoSyntax.parseDef  

    // Perform the actions:
    for (action <- actions) {
      action match {
        case EXECUTE => engineMode match {
          case ENGINE_DENOTATIONAL => {
            val interp = new LambdoInterpreter
            for (d <- defs) {
              println(interp.process(d))
              println()
            }
          }          
          case ENGINE_OPERATIONAL => {
            val machine = new LambdoMachine

            machine.process(defs)
            
            while (machine.ThreadPool.isMainThreadRunning) {
              machine.ThreadPool.waitForInactivity()
            }
            machine.ThreadPool.stop()
          }
        }
      }
    }
  }
}




object LambdoTest {

  def main (args : Array[String]) {
    
  }
}
