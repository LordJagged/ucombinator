// TODO: Add a flag to allow range-based or free-based Abstract GC.

package org.ucombinator.project.hofa ; 

import org.ucombinator.project.lambdo._ ;

import org.ucombinator.languages.sexp._ ;
import org.ucombinator.languages.json._ ;
import org.ucombinator.math.order._ ;
import org.ucombinator.util.{HashCanonicalizer} ;


import scala.collection.immutable.{SortedMap,TreeMap} ;
import scala.collection.immutable.{SortedSet,TreeSet} ;





object AbstractCommon {

  private [hofa] var useRangeBasedTouching = true

  import LambdoSyntax._

  trait Loc extends TagOrdered[Loc] with JSONable {
    def orderTag = this.getClass().getName()
    def localCompare (loc2 : Loc) : Int ;

    /**
     Answers whether this abstract location represents only one concrete location by definition.
     */
    def isSingleton : Boolean ;

    override def hashCode() : Int = throw new Exception("hashCode method undefined in " + this.getClass().getName())
    override def equals (that : Any) : Boolean = (this compare (that.asInstanceOf[Loc])) == 0
      //throw new Exception("equals method undefined in " + this.getClass().getName())
  }

  object Loc extends FlatOrder[Loc] {
    private var maxNat = 0

    def allocNat() : Loc = {
      maxNat += 1
      NatLoc(maxNat)
    }
  }

  case object HaltLoc extends Loc with LocallySingletonOrdered[Loc] {
    def isSingleton = true

    override val hashCode : Int = 23 ;
    override def toJSON() : JSONExp = JSONSyntax.S("HaltLoc")
  }

  /**
   A VarLoc object is designed to represent all of the addresses to
   which a particular variable may be bound.
   */
  case class VarLoc(val variable : Var) extends Loc {
    def isSingleton = false

    def localCompare (that : Loc) = this.variable compare that.asInstanceOf[VarLoc].variable
    
    override lazy val hashCode : Int = variable.hashCode()

    def toJSON() : JSONExp = {
      import JSONSyntax._
      F("VarLoc",List(T(variable.name)))
    }
  }


  /**
   An ExpLoc object associates an abstract address with an expression.

   What it represents depends on the implementation and its use.
   */
  case class ExpLoc(val exp : Exp) extends Loc {
    def isSingleton = false
    def localCompare (that : Loc) = this.exp compare that.asInstanceOf[ExpLoc].exp
    
    override lazy val hashCode : Int = exp.hashCode()

    def toJSON() : JSONExp = {
      import JSONSyntax._
      F("ExpLoc",List(exp.toJSON()))
    }
  }

  
  /**
   A FieldLoc object represents a memory location for the field of an object.
   */
  case class FieldLoc(field : Field, oLoc : Loc) extends Loc {
    def isSingleton = oLoc.isSingleton

    def localCompare (that : Loc) : Int = that match {
      case FieldLoc(field2,oLoc2) => 
        TotalOrder.compare[Field,Loc,org.ucombinator.languages.SyntaxNode,Loc] (field,oLoc) (field2,oLoc2)
        //TotalOrder.lexicographicComparison (field,oLoc) (field2,oLoc2)
    }
    
    override lazy val hashCode : Int = field.hashCode() + 2 * oLoc.hashCode()
    override def equals (that : Any) = that match {
      case fl2 : FieldLoc => (this compare fl2) == 0
      case _ => false
    }

    def toJSON() : JSONExp = {
      import JSONSyntax._
      F("FieldLoc",List(field.toJSON(), oLoc.toJSON()))
    }
  }


  case class NatLoc (n : Int) extends Loc {
    def isSingleton = true

    def localCompare (l2 : Loc) : Int = l2 match {
      case NatLoc(n2) => n compare n2
    }

    override def hashCode = n

    def toJSON() : JSONExp = {
      import JSONSyntax._
      F("NatLoc",List(Z(n)))
    }
  }


  trait BEnv extends Ordered[BEnv] with JSONable {
    def + (v : Var, loc : Loc) : BEnv ;
    def ++ (vls : Iterable[(Var,Loc)]) : BEnv ;

    /**
     Produces an identical binding environment, except its domain is restricted to the argument.
     */
    def / (vars : Iterable[Var]) : BEnv ;

    def apply(k : Var) : Loc ;
    def get (k : Var) : Option[Loc] ;
    def getOrElse (k : Var, dflt : Loc) : Loc ;

    def toMap : Map[Var,Loc] ;

    override def hashCode() : Int = throw new Exception("hashCode() not implemented in " + this.getClass().getName())
    override def equals(a : Any) : Boolean = throw new Exception("equals() not implemented in " + this.getClass().getName())

    def toJSON() : JSONExp = {
      import JSONSyntax._

      F("BEnv",List(JSON(toMap)))
    }
  }


  // object Val extends HashCanonicalizer[Val] 
  trait Val extends TagOrdered[Val] with JSONable {
    def localCompare (val2 : Val) : Int ;
    def orderTag = this.getClass().getName() 

    def touches(store : Store) : List[Loc] = {
      throw new Exception("touches() not yet implemented in " + this.getClass().getName())
    }

    override def hashCode() : Int = throw new Exception("hashCode() not yet implemented in " + this.getClass().getName())
    override def equals (a : Any) = (this compare a.asInstanceOf[Val]) == 0

    def toJSON() : JSONExp = throw new Exception("toJSON() not yet implemented in " + this.getClass().getName())
  }

  trait KontMark extends TagOrdered[KontMark] {
    def toJSON()  : JSONExp ;
    def orderTag = this.getClass().getName()

    override def hashCode : Int = throw new Exception("hashCode not yet implemented in " + this.getClass().getName())
    
    override def equals(a : Any) = a match {
      case that : KontMark => (this compare that) == 0
    }
  }

  case object EmptyMark extends KontMark {
    def localCompare (that : KontMark) = 0
    def toJSON() = JSONSyntax.S("EmptyMark")

    override def hashCode : Int = 1
  }



  abstract class ProcCall extends TagOrdered[ProcCall] {
    def orderTag = this.getClass().getName()

    def toJSON() : JSONExp ;

    override def hashCode : Int = throw new Exception("hashCode not yet implemented in " + this.getClass().getName())

    override def equals (a : Any) = a match {
      case that : ProcCall => (this compare that) == 0
    }
  }

  case class MonoProcCall(lam : Lambda) extends ProcCall {
    def localCompare (that : ProcCall) : Int = that match {
      case MonoProcCall (lam2) => lam compare lam2
    }

    override lazy val hashCode : Int = lam.hashCode()

    def toJSON() : JSONExp = JSONSyntax.F("MonoProcCall", List(lam.toJSON()))

    override def toString() : String = "lam" + lam.label
  }


  case class CallMark(val calls : scala.collection.immutable.SortedSet[ProcCall]) extends KontMark {
    def localCompare (that : KontMark) = that match {
      case CallMark(calls2) => TotalOrder.compare (calls) (calls2) (TotalOrder.orderIdentity)
    }

    override lazy val hashCode : Int = calls.foldRight (0) { case (p,hash) => p.hashCode() + 2*hash }
    
    def toJSON() = JSONSyntax.F("CallMark",calls.toList map (_.toJSON()))

    def + (call : ProcCall) : CallMark = CallMark(calls + call)
  }

  case object EmptyCallMark extends CallMark(scala.collection.immutable.TreeSet[ProcCall]()(TotalOrder.orderIdentity[ProcCall]))


  /**
   A Proc object represents a closure or a primitive operation.
   */
  trait Proc extends Val

  /**
   A Bas object represents a basic value.
   */
  trait Bas extends Val {
    override def touches(store : Store) = List()
  }

  /**
   A Kont object represents a continuation.
   */
  trait Kont extends Val {
    def mark : KontMark ;
    def mark_= (mark : KontMark) : Kont ;

    def stackTouches (store : Store) : List[Kont] ;
  }

  /**
   A HaltKont object represents the "halt" continuation.
   */
  case class HaltKont(val mark : KontMark) extends Kont with LocallySingletonOrdered[Val] {
    override def touches(store : Store) = List()

    def mark_= (newMark : KontMark) : Kont = HaltKont(newMark)

    def stackTouches (store : Store) : List[Kont] = List()

    override val hashCode : Int = 10
    override def toJSON() = JSONSyntax.S("HaltKont")
  }

  
  /**
   A KontLet1 object encodes the return point of let form.
   */
  case class KontLet1(val v : Var, val exp : Exp, val bEnv : BEnv, val kontp : Loc, val mark : KontMark) extends Kont {

    def mark_= (newMark : KontMark) : Kont =
      KontLet1(v,exp,bEnv,kontp,newMark)

    override def touches(store : Store) : List[Loc] = 
      if (useRangeBasedTouching) 
        (kontp :: (bEnv.toMap.toList map (_._2)))
      else 
        (kontp :: ((exp.freeVars - v).toList map ((v : Var) => bEnv(v))))

    def stackTouches (store : Store) : List[Kont] = {
      store(kontp).toList.asInstanceOf[List[Kont]]
    }

    def localCompare(that : Val) : Int = {
      val kont2 = that.asInstanceOf[KontLet1]
      val c = v compare kont2.v
      if (c != 0)
        return c
      val c2 = exp compare kont2.exp
      if (c2 != 0)
        return c2
      val c3 = kontp compare kont2.kontp
      if (c3 != 0)
        return c3
      val c4 = mark compare kont2.mark
      if (c4 != 0)
        return c4
      bEnv compare kont2.bEnv
    }
    
    override lazy val hashCode : Int =
      mark.hashCode() * 5 + v.hashCode() * 4 + exp.hashCode() * 3 + bEnv.hashCode() * 2 + kontp.hashCode()

    override def toJSON() : JSONExp = {
      import JSONSyntax._
      
      F("KontLet1",List(O(Map("v" -> v.toJSON(), 
                              "exp" -> exp.toJSON(),
                              "bEnv" -> bEnv.toJSON(),
                              "kontp" -> kontp.toJSON(),
                              "mark" -> mark.toJSON()))))
    }
  }


  object Clo {
    //def apply (lam : Lambda, bEnv : BEnv) = (Val(new Clo(lam,bEnv))).asInstanceOf[Clo]
    def apply (lam : Lambda, bEnv : BEnv) = new Clo(lam,bEnv)
    def unapply (clo : Clo) = Some((clo.lam,clo.bEnv))
  }

  class Clo(val lam : Lambda, val bEnv : BEnv) extends Proc {
    override def touches (store : Store) =
      if (useRangeBasedTouching)
        (bEnv.toMap.toList map (_._2))
      else
        (lam.freeVars.toList map ((v : Var) => bEnv(v)))

    def localCompare(v : Val) : Int = {
      val clo2 = v.asInstanceOf[Clo]
      val c = lam compare clo2.lam
      if (c != 0)
        return c
      bEnv compare clo2.bEnv
    }
    override lazy val hashCode : Int = lam.hashCode() * 2 + bEnv.hashCode()
    override def toString = "<" + lam + "," + bEnv + ">"

    override def toJSON() : JSONExp = {
      import JSONSyntax._
      
      F("Clo",List(O(Map("lam" -> lam.toJSON(), 
                         "bEnv" -> bEnv.toJSON()))))
    }
  }


  case class Record (val oLoc : Loc, val fields : scala.collection.immutable.SortedMap[Field,Loc]) extends Val {
    def localCompare (that : Val) : Int = that match {
      case Record(oLoc2,fields2) => {
        val cmp = oLoc compare oLoc2
        if (cmp != 0)
          return cmp
        TotalOrder.compare (fields) (fields2)
      }
    }
    override def touches(store : Store) = fields.toList map (_._2)
    override lazy val hashCode : Int = fields.foldRight (0) { case ((f,loc),hash) => f.hashCode() + loc.hashCode() + 2*hash }
  }


  /* Contexts. */

  /**
   Traditionally, an abstract context encodes a bounded history of the computation.
   */
  trait Context extends Ordered[Context] with JSONable {

    def localCompare (k2 : Context) : Int ;
    def compare (k2 : Context) : Int = {
      val c1 = this.getClass().getName().compare(k2.getClass.getName()) 

      if (c1 != 0)
        return c1

      localCompare(k2)
    }
    
    def toJSON() : JSONExp = throw new Exception("toJSON() not yet implemented for " + this.getClass().getName())
  }

  /**
   A MonoContext encodes absolutely no computational history.
   */
  case object MonoContext extends Context {
    def localCompare (c2 : Context) : Int = 0

    override def hashCode() = 1
    override def equals(o : Any) = this eq o.asInstanceOf[AnyRef]

    override def toJSON() : JSONExp = JSONSyntax.S("MonoContext")
  }


  /**
   NatContext provides an arbitrary number of contexts, possibly enabling recovery of the concrete semantics from the abstract semantics.
   */

  case class NatContext(n : Int) extends Context {
    def localCompare (c2 : Context) = c2 match {
      case NatContext(n2) => n compare n2
    }

    override def hashCode() = n
    override def equals(o : Any) = o match {
      case NatContext(n2) => n == n2
      case _ => false
    }
  }




  /**
   A primitive value must be a trivially evaluable, such as a PrimOp.
   */
  case class Op(val op : Exp) extends Proc {
    override def touches(store : Store) = List()

    def localCompare(that : Val) = op compare that.asInstanceOf[Op].op
    override lazy val hashCode : Int = op.hashCode()

    override def toJSON() : JSONExp = JSONSyntax.F("Op",List(op.toJSON()))
  }

  trait LocallySingletonOrdered[A] {
    def localCompare (a : A) : Int = 0
  }

  case object VoidVal extends Bas with LocallySingletonOrdered[Val] {
    override def hashCode() : Int = 1
    override def toJSON() = JSONSyntax.S("VoidVal")
  }
  abstract class BoolVal extends Bas with LocallySingletonOrdered[Val]
  case object TrueVal extends BoolVal {
    override def hashCode() : Int = 2
    override def toJSON() = JSONSyntax.S("TrueVal")
  }
  case object FalseVal extends BoolVal {
    override def hashCode() : Int = 3
    override def toJSON() = JSONSyntax.S("FalseVal")
  }
  case object NilVal extends Bas with LocallySingletonOrdered[Val] {
    override def hashCode() : Int = 4
    override def toJSON() = JSONSyntax.S("NilVal")
  }
  abstract class Num extends Bas 
  case object ANum extends Num with LocallySingletonOrdered[Val] {
    override def hashCode() : Int = 5
    override def toJSON() = JSONSyntax.S("ANum")
  }
  case object StringVal extends Bas with LocallySingletonOrdered[Val] {
    override def hashCode() : Int = 7
    override def toJSON() = JSONSyntax.S("StringVal")
  }
  case class ExactInt(z : BigInt) extends Num {
    def localCompare (o : Val) : Int = z compare o.asInstanceOf[ExactInt].z 
    override def hashCode() : Int = z.hashCode()
  }

  

  
  implicit def scalaToLambdo(b : Boolean) : Bas = 
    if (b) {
      TrueVal
    } else {
      FalseVal
    }

  // Pattern matching on singleton values:
  object DSingle {
    def unapply (d : D) : Option[Val] = 
      if (d.size == 1) {
        Some(d.toList.head)
      } else {
        None
      }
  }
  



  trait D extends JSONable {
    def size : Int ;
    def toList : List[Val] ;
    
    def + (v : Val) : D ;
    def join (d2 : D) : D ;
    
    def elements : Iterable[Val] ;

    def isSubsumedBy (d2 : D) : Boolean ;

    override def hashCode() : Int = throw new Exception("hashCode() not implemented for D")
    override def equals(a : Any) : Boolean = throw new Exception("equals() not implemented for D")

    override def toJSON() = {
      JSON.fromIterable(elements)
    }
  }
  
  def mustBeTrue(d : D) : Boolean = {
    for (v <- d.elements) {
      if (v eq FalseVal)
        return false
    }
    // BUG: What if d is empty?
    return true
  }

  def mustBeFalse(d : D) : Boolean = {
    if (d.size != 1)
      return false

    for (v <- d.elements) {
      if (v eq FalseVal)
        return true
    }

    return false
  }
  
  private case class StoreEntry (val loc : Loc, value : Val) {
    override lazy val hashCode : Int = {
      loc.hashCode() * 2 + value.hashCode()
    }
    override def equals(that : Any) = that match {
      case StoreEntry(loc2,value2) => (loc equals loc2) && (value equals value2)
      case _ => false
    }
  }

  
  trait StoreHash {
    def join (that : StoreHash) : StoreHash ;
    def join (loc : Loc, d : D) : StoreHash ;
    def isWeakerThan (that : StoreHash) : Boolean ;
  }

  class ArrayStoreHash(val array : Array[Long], val length : Int) extends StoreHash {
    def apply(i : Int) = array(i)

    override def toString = array.take(length).toList.toString

    def join (loc : Loc, d : D) : ArrayStoreHash = {
      join(ArrayStoreHash(loc,d))
    }


    def join (other : StoreHash) : ArrayStoreHash = {
      val that = other.asInstanceOf[ArrayStoreHash]
      ArrayStoreHash.join(this,that)
    }

    def isWeakerThan (other : StoreHash) : Boolean = {
      val that = other.asInstanceOf[ArrayStoreHash]

      if (length == 0)
        // Empty -- trivially weaker.
        return true 

      var ai = 0 
      var bi = 0
      val b = that.array
      val blength = b.length
      val alength = this.length

      val a = array

      var av : Long = 0

      while (bi < blength && ai < alength) {
        av = a(ai)
        val cmp = av - b(bi)

        if (cmp < 0) {
          // a(ai) < b(bi): We've gone past!
          // Proof: if a(n) < b(m), then a(n) < b(m+1)
          return false
        }
        else if (cmp == 0) {
          // Found it a(ai) == b(bi)
          ai = ai + 1
          bi = bi + 1
        } else {
          // a(ai) > b(bi): We may still find it.
          // Proof: a(ai) - b(bi) > a(ai) - b(bi+1)
          bi = bi + 1
        }
      }

      if (ai == alength) {
        // We found everything!
        return true
      } 

      return false
    }
  }


  object ArrayStoreHash {

    private object StoreEntries {
      
      private var max : Long = 0 
      
      private val table = scala.collection.mutable.HashMap[StoreEntry,Long]()
      
      private def allocate () : Long = {
        synchronized {
          max = max + 1
          max
        }
      }
      
      def apply(loc : Loc, value : Val) : Long = {
        val entry = StoreEntry(loc,value)
        table get entry match {
          case Some(l) => l
          case None => {
            val next = allocate()
            table(entry) = next
            next
          }
        }
      }
    }
    

    def apply() : ArrayStoreHash = new ArrayStoreHash(new Array(0),0)
    
    def apply(loc : Loc, v : Val) : Long = StoreEntries(loc,v)
    
    def apply(loc : Loc, d : D) : ArrayStoreHash = {
      val a : Array[Long] = new Array[Long](d.size)
      var ai = 0
      for (v <- d.toList) {
        a(ai) = this(loc,v)
        ai = ai + 1
      }
      scala.util.Sorting.quickSort(a)
      new ArrayStoreHash(a,a.length)
    }

    def apply(entries : Iterable[(Loc,D)]) : ArrayStoreHash = {
      // TODO: Speed this up.
      var hash = ArrayStoreHash()
      for ((l,d) <- entries) {
        hash = join(hash,apply(l,d))
      }
      hash
    }

    def join (a : ArrayStoreHash, b : ArrayStoreHash) : ArrayStoreHash = {
      val c = new Array[Long](a.length + b.length)
      var ai = 0 
      var bi = 0
      var ci = 0
      while (ai < a.length && bi < b.length) {
        val cmp = a(ai) compare b(bi)
        var v = a(ai)
        if (cmp < 0) { // a[ai] < b[bi]
          ai = ai + 1
        } else if (cmp == 0) { // a[ai] == b[bi]
          ai = ai + 1
          bi = bi + 1
        } else { // a[ai] > b[bi]
          v = b(bi)
          bi = bi + 1
        }
        c(ci) = v
        ci = ci + 1
      }
      while (ai < a.length) {
        c(ci) = a(ai)
        ci = ci + 1
        ai = ai + 1
      }
      while (bi < b.length) {
        c(ci) = b(bi)
        ci = ci + 1
        bi = bi + 1
      }
      new ArrayStoreHash(c,ci)
    }
  }

  
  trait Store extends JSONable {
    def apply(l : Loc) : D ;
    def get (l : Loc) : Option[D] ;
    def getOrElse (l : Loc, dflt : D) : D ;

    /**
     Adds a location-value pair to the store.

     If the location already exists, then its current value is joined with its new value.

     Used when the address being added has been freshly allocated.
    */    
    def + (l : Loc, d : D) : Store ;


    /**
     Adds several location-value pairs to the store.
     */
    def ++ (lds : Iterable[(Loc,D)]) : Store ;
    def join (s2 : Store) : Store ;


    /**
     Forcibly overwrites a location in the store with the new value.  

     The old value is discarded.

     <b>Warning</b>: This method can lead to unsoundness if not used properly.  
        Use weakUpdate in the absence of a soundness proof.
     <p>
     See: Might and Shivers. Exploiting reachability and cardinality in abstract interpretation.  Journal of Functional Programming.  2008.
     </p>
     */  
    def strongUpdate(l : Loc, d : D) : Store ;



    /**
     Updates a location in the store with a join of the new and old values for that location.
     */
    def weakUpdate(l : Loc, d : D) : Store ;


    /**
     Updates a location with a new value.

     The update should be strong if the store has enough information to prove that it is sound, and weak otherwise.
     */
    def update(l : Loc, d : D) : Store ;

    
    def isSubsumedBy(s2 : Store) : Boolean ;
    def toList : List[(Loc,D)]

    override def hashCode() : Int = throw new Exception("hashCode() not implemented for " + this.getClass().getName())
    override def equals(a : Any) : Boolean = throw new Exception("equals() not implemented for " + this.getClass().getName())

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      val entries = for ((l,d) <- this.toList) yield {
        F("Entry",List(l.toJSON(),d.toJSON()))
      }
      F("Store",entries)
    }
  }

  
}



trait WideningDegree
case object SingleWidening extends WideningDegree
case object PerFlatWidening extends WideningDegree
case object NoWidening extends WideningDegree






/**
 StandardDomains provides a default implementation of common data structures.

 They are asymptotically efficient data-structures based on balanced trees.
 */
object StandardDomains {

  import AbstractCommon._
  import LambdoSyntax.Var

  case object MonoBEnv extends BEnv {
    def + (v : Var, loc : Loc) : BEnv = this
    def ++ (vls : Iterable[(Var,Loc)]) = this
    def / (vars : Iterable[Var]) = this

    def apply(v : Var) : Loc = VarLoc(v)
    def get (v : Var) : Option[Loc] = Some(VarLoc(v))
    def getOrElse (v : Var, dflt : Loc) : Loc = VarLoc(v)

    def toMap = throw new Exception("Can't convert MonoBEnv to Map")

    def compare(that : BEnv) = 0
    override val hashCode : Int = 1
    override def equals(a : Any) = true
    
    override def toJSON() : JSONExp = JSONSyntax.S("MonoBEnv")
  }


  class StdBEnv(val map : SortedMap[Var,Loc]) extends BEnv {
    def + (v : Var, l : Loc) : BEnv = new StdBEnv(map(v) = l)
    def ++ (vls : Iterable[(Var,Loc)]) : BEnv = new StdBEnv(map ++ vls)
    def / (vars : Iterable[Var]) : BEnv = {
      var map_ = TreeMap[Var,Loc]()(LambdoSyntax.varToOrdered)
      for (v <- vars) {
        map_ = map_(v) = map(v)
      }
      new StdBEnv(map_)
    }

    def apply(k : Var) : Loc  = map(k)
    def get (k : Var) : Option[Loc] = map.get(k)
    def getOrElse (k : Var, dflt : Loc) : Loc = map.getOrElse(k,dflt)

    def toMap : Map[Var,Loc] = map

    def compare (otherBEnv : BEnv) : Int = {
      var lst1 = map.toList
      var lst2 = otherBEnv.asInstanceOf[StdBEnv].map.toList

      while (!lst1.isEmpty) {
        if (lst2.isEmpty)
          return 1
        
        val (v1,l1) = lst1.head
        val (v2,l2) = lst2.head

        val cmp1 = v1 compare v2
        
        if (cmp1 != 0)
          return cmp1
        
        val cmp2 = l1 compare l2

        if (cmp2 != 0)
          return cmp2

        lst1 = lst1.tail
        lst2 = lst2.tail
      }

      if (!lst2.isEmpty)
        return -1 

      0
    }

    override lazy val hashCode : Int = map.foldRight (0) { case ((v,loc),hash) => v.hashCode() + loc.hashCode() + 2*hash }
    override def equals(a : Any) : Boolean = (this compare a.asInstanceOf[BEnv]) == 0

    override def toString = map.toString
  }

  val botBEnv = new StdBEnv(new TreeMap[Var,Loc]()(LambdoSyntax.varToOrdered _))



  class StdStore(val map : TreeMap[Loc,D]) extends Store {
    lazy val toList = map.toList

    def apply(l : Loc) = map(l)
    def get (l : Loc) : Option[D] = map.get(l)
    def getOrElse (l : Loc, dflt : D) : D = map.getOrElse(l,dflt) 

    def isSubsumedBy (that : Store) : Boolean = {
      for ((l1,d1) <- map) {
        that get l1 match {
          case Some (d2) => if (!(d1 isSubsumedBy d2)) return false
          case None => return false
        }
      }
      return true      
    }

    def + (loc : Loc, d : D) : Store = {
      map get loc match {
        case Some(d2) => new StdStore(map(loc) = d join d2)
        case None => new StdStore(map(loc) = d)
      }
    }
    
    def ++ (lds : Iterable[(Loc,D)]) : Store = {
      var cur : Store = this
      for ((l,d) <- lds) {
        cur = cur + (l,d)
      }
      cur
    }

    def join (otherStore : Store) : Store = {
      val s2 = otherStore.asInstanceOf[StdStore]
      s2 ++ map
    }

    def strongUpdate(l : Loc, d : D) : Store = {
      val newMap = (map - l)(l) = d
      
      new StdStore(newMap)
    }

    def weakUpdate(l : Loc, d : D) : Store = {
      // We don't track cardinalities in this very basic store
      // implemenation, so we can use addition.

      // If we tracked cardinalities, we'd keep cardinality info the
      // same, but still update the value.
      this + (l,d)
    }

    def update(l : Loc, d : D)  : Store = {
      if (l.isSingleton) {
        strongUpdate(l,d)
      } else {
        weakUpdate(l,d)
      }
    }

    override lazy val hashCode : Int = map.foldRight (0) { case ((loc,d),hash) => loc.hashCode() + d.hashCode() + 2*hash }
    override def equals(a : Any) : Boolean = map equals a.asInstanceOf[StdStore].map

    override def toString = map.toString
  }

  val botStore = new StdStore(new TreeMap[Loc,D])




  class StdD(val set : SortedSet[Val]) extends D {
    val size = set.size
    lazy val toList = set.toList

    def + (v : Val) : D = 
      new StdD(set + v)

    def join (otherD : D) : D = {
      val d2 = otherD.asInstanceOf[StdD]
      new StdD(set ++ d2.set)
    }
    
    def elements : Iterable[Val] = set

    def isSubsumedBy(otherD : D) : Boolean = {
      // TODO/BUG: Make this smarter in case the partial order on Val is not flat
      for (v <- set) {
        if (!otherD.toList.contains(v))
          return false
      }
      return true
    }

    override lazy val hashCode : Int = set.foldRight (0) { case (el,hash) => el.hashCode() + 2*hash }
    override def equals (that : Any) : Boolean = this.set equals that.asInstanceOf[StdD].set
    
    override def toString = set.toString
  }

  val botD = new StdD(new TreeSet[Val])

}



object HashingDomains {

  import AbstractCommon._
  import LambdoSyntax.Var

  class ArrayHashingStore(val map : TreeMap[Loc,D], val hash : StoreHash) extends Store {
    lazy val toList = map.toList

    def apply(l : Loc) = map(l)
    def get (l : Loc) : Option[D] = map.get(l)
    def getOrElse (l : Loc, dflt : D) : D = map.getOrElse(l,dflt) 

    private def isSubsumedBy_iterative (that : Store) : Boolean = {
      for ((l1,d1) <- map) {
        that get l1 match {
          case Some (d2) => if (!(d1 isSubsumedBy d2)) return false
          case None => return false
        }
      }
      return true      
    }
    

    def isSubsumedBy(otherStore : Store) : Boolean = {
      if (otherStore.isInstanceOf[ArrayHashingStore]) {
        val that = otherStore.asInstanceOf[ArrayHashingStore]
        val result = this.hash isWeakerThan that.hash
        if (HOFA.sanityChecking) {
          val result2 = isSubsumedBy_iterative(otherStore)
          if (result != result2)
            throw new Exception("Sanity check failed ("+result+"/"+result2+")\n" + this + "\n\n v.\n\n" + otherStore)
        }
        return result
      }

      isSubsumedBy_iterative(otherStore)
    }

    def + (loc : Loc, d : D) : Store = {
      map get loc match {
        case Some(d2) => new ArrayHashingStore(map(loc) = d join d2, hash join (loc,d))
        case None => new ArrayHashingStore(map(loc) = d, hash join (loc,d))
      }
    }
    
    def ++ (lds : Iterable[(Loc,D)]) : Store = {
      var cur : Store = this
      for ((l,d) <- lds) {
        cur = cur + (l,d)
      }
      cur
    }

    def join (otherStore : Store) : Store = {
      val s2 = otherStore.asInstanceOf[ArrayHashingStore]
      s2 ++ map
    }

    def strongUpdate(l : Loc, d : D) : Store = {
      val newMap = (map - l)(l) = d
      
      new ArrayHashingStore(newMap,ArrayStoreHash(newMap))
    }

    def weakUpdate(l : Loc, d : D) : Store = {
      // We don't track cardinalities in this very basic store
      // implemenation, so we can use addition.

      // If we tracked cardinalities, we'd keep cardinality info the
      // same, but still update the value.
      this + (l,d)
    }

    def update(l : Loc, d : D)  : Store = {
      if (l.isSingleton) {
        strongUpdate(l,d)
      } else {
        weakUpdate(l,d)
      }
    }

    override lazy val hashCode : Int = map.foldRight (0) { case ((loc,d),hash) => loc.hashCode() + d.hashCode() + 2*hash }
    override def equals(a : Any) : Boolean = map equals a.asInstanceOf[ArrayHashingStore].map

    override def toString = map.toString
  }

  val botStore = new ArrayHashingStore(new TreeMap[Loc,D],ArrayStoreHash())  
  
}






abstract class UniversalCFAFramework extends MonotoneTransitionSystem {
  import AbstractCommon._
  import LambdoSyntax._


  /* Parameters. */
  def botBEnv : BEnv ;
  def botStore : Store ;
  def botD : D ;

  type K <: Context

  var wideningDegree : WideningDegree = NoWidening
  var useAbstractGarbageCollection = true
  var useBindingEnvironmentRestriction = true
  

  /**
   Evaluates pure primitive operations in the abstract.
 
   Override this method to set the precision of primitive operations.
   */
  def primEval (p : PPrimOp, argVals : List[D]) : D = (p,argVals) match {
    case (PPrimOp("+"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 + z2))
    case (PPrimOp("-"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 - z2))
    case (PPrimOp("*"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 * z2))
    case (PPrimOp("/"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 / z2))
    case (PPrimOp("="),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 equals z2)
    case (PPrimOp("<"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 < z2)
    case (PPrimOp(">"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 > z2)
    case (PPrimOp("="),_) => mkD(TrueVal, FalseVal)
    case (PPrimOp("<"),_) => mkD(TrueVal, FalseVal)
    case (PPrimOp("<="),_) => mkD(TrueVal, FalseVal)
    case (PPrimOp(">"),_) => mkD(TrueVal, FalseVal)
    case (PPrimOp("+"),_) => mkD(ANum)
    case (PPrimOp("-"),_) => mkD(ANum)
    case (PPrimOp("*"),_) => mkD(ANum)
    case (PPrimOp("/"),_) => mkD(ANum)
    case (PPrimOp("modulo"),_) => mkD(ANum)
    case (PPrimOp("quotient"),_) => mkD(ANum)
    case (PPrimOp("gcd"),_) => mkD(ANum)
    case (PPrimOp("random-range"),_) => mkD(ANum)
    case (PPrimOp("random-byte"),_) => mkD(ANum)
    case (PPrimOp("not"),_) => mkD(TrueVal,FalseVal)
    case (PPrimOp("odd?"),_) => mkD(TrueVal,FalseVal)
    case (PPrimOp("even?"),_) => mkD(TrueVal,FalseVal) 

    case _ => throw new Exception("unknown primop: " + p + ", with arguments: " + argVals)
  }


  /**
   Converts a literal expression into an abstract value.

   The default implementation uses finite abstract sets.

   Override this method to use infinite abstract sets.
   */
  def litEval (exp : LitExp) : D = exp match {
    case IntLit(_) => mkD(ANum)
    case VoidLit() => mkD(VoidVal)
    case BoolLit(true) => mkD(TrueVal)
    case BoolLit(false) => mkD(FalseVal)
    case NilLit() => mkD(NilVal)
    case TextLit(_) => mkD(StringVal)
  }


  /**
   Evaluates an atomic expression with respect to a binding environment and a store to return a value.

   An atomic expression, in this case, is one whose evaluation must terminate and which produces no side effects.
   */
  protected def atomEval (be : BEnv, store : Store) (exp : Exp) : D = exp match {
    case lit : LitExp => litEval(lit)
    case lam @ Lambda(args,body) => 
      mkD(Clo(lam,if (useBindingEnvironmentRestriction) 
                    { be / lam.freeVars } 
                  else
                    { be }))
    case App(p : PPrimOp, args) => primEval(p, args map (atomEval (be,store)))
    case Ref(v) => be get v match {
      case Some(loc) => store get loc match {
        case Some(d) => d
        case None => {
          throw new Exception("No store entry for " + v + " @ " + loc)
        }
      }
      case None => throw new Exception("No env entry for " + v) 
    }
    case p : PrimOp => mkD(Op(p))
    case cps @ CPS(p : PrimOp) => mkD(Op(cps))
    case _ => throw new Exception("Cannot eval: " + exp)
  }


  
  private[hofa] def mkD(vals : Val*) : D = {
    var d = botD
    for (v <- vals) {
      d = d + v
    }
    d
  }

  private[hofa] def mkD(vals : List[Val]) : D = {
    var d = botD
    for (v <- vals) {
      d = d + v
    }
    d
  }
  
  
  
  private object StateTable {
    
    private val table = scala.collection.mutable.HashMap[AbstractState,Long]()
    
    private var maxSerial : Long = 0 ;
    
    private def nextSerial() : Long = {
      synchronized {
        maxSerial = maxSerial + 1
        maxSerial 
      }
    }

    def apply(state : AbstractState) : Long = {
      (table get state) match {
        case Some(sn) => sn
        case None => {
          val sn = nextSerial()
          table(state) = sn
          sn
        }
      }
    }
  }


  private [hofa] abstract class Flat {
    override def hashCode() : Int = 
      throw new Exception("hashCode() not yet implemented for " + this.getClass().getName())

    override def equals(a : Any) : Boolean = 
      throw new Exception("equals() not yet implemented for " + this.getClass().getName())
  }

  private [hofa] case class Sharp (val store : Store) {
    override lazy val hashCode : Int =
      store.hashCode()
    override def equals(a : Any) : Boolean = a match {
      case Sharp(store2) => store equals store2
    }
  }


  private [hofa] case object SharpOrder extends BoundedLattice[Sharp] {
    override def weakerThan (sharp1 : Sharp, sharp2 : Sharp) : Boolean = sharp1.store isSubsumedBy sharp2.store
    override def join (sharp1 : Sharp, sharp2 : Sharp) : Sharp = {
      Sharp(sharp1.store join sharp2.store)
    }

    val bot : Sharp = Sharp(botStore)
    def top : Sharp = throw new Exception("No top sharp in abstract CPS")
  }


  abstract class AbstractState extends MonotoneNode[Flat,Sharp] with Registerable with JSONable {
    lazy val serial : Long = StateTable(this)

    def isGarbageCollectable : Boolean ;

    def toJSON() : JSONExp = throw new Exception("toJSON() not yet implemented for " + this.getClass().getName())

    def store : Store ;
    def store_= (store : Store) : AbstractState ;

    def touches : List[StoreNode] = throw new Exception("touches not yet implemented in " + this.getClass().getName())

    override lazy val hashCode : Int = flat.hashCode() * 2 + sharp.hashCode()
    override def equals(that : Any) : Boolean = that match {
      case state2 : AbstractState => (this.flat equals state2.flat) && (this.sharp equals state2.sharp)
      case _ => false
    }    
  }

  
  

  /* MonotoneTransitionSystem requirements. */
  type F = Flat
  type S = Sharp

  def sharpOrder = SharpOrder

  type N = AbstractState
  



  /* Abstract garbage collection utilities. */
  
  
  
  class StackGraph(val store0 : Store) extends ImplicitGraph {

    type N = Kont
    
    val seen = scala.collection.mutable.HashSet[Kont]()

    def mark (n : N) : Unit = {
      seen += n
    }

    def seen (n : N) : Option[N] = {
      if (seen.contains(n))
        Some(n)
      else
        None
    }

    def succ (n : N) : List[N] = {
      n.stackTouches(store0) 
    }
  }


  trait StoreNode
  case class LocNode(val loc : Loc) extends StoreNode
  case class ValNode(val value : Val) extends StoreNode


  class StoreGraph(val store0 : Store) extends ImplicitGraph {
    
    type N = StoreNode
    
    var reachable : Store = botStore ;
    
    def mark (n : N) : Unit = n match {
      case LocNode(loc) => {
        reachable = reachable + (loc,store0(loc))
      }
      case ValNode(value) => {
      }
    }

    
    def seen (n : N) : Option[N] = n match {
      case LocNode(loc) => {
        (reachable get loc) match {
          case Some(_) => Some(n)
          case _ => None
        }
      }
      case ValNode(value) => {
        None
      }      
    }
    
    def succ (n : N) : List[N] = n match {
      case LocNode(loc) => {
        store0(loc).toList map (ValNode(_))
      }
      case ValNode(value) => {
        value.touches(store0) map (LocNode(_))
      }
    }
  }
  
  private def reachable(state : AbstractState) : Store = {
    val sg = new StoreGraph(state.store)
    sg.explore(state.touches)
    sg.reachable
  }
  

  protected def gc(state : AbstractState) : AbstractState = 
    if (state.isGarbageCollectable) {
      state.store = reachable(state)
    } else {
      state
    }

  
  override def narrow(state : AbstractState) = 
    if (useAbstractGarbageCollection) 
      { gc(state) }
    else
      { state }

  
}




abstract class UniversalCFA_ANF extends UniversalCFAFramework {

  import AbstractCommon._
  import LambdoSyntax._


  def initMark : KontMark ;
  var kontMarkingEnabled : Boolean = true ;

  /**
   Modifies the continuation mark when a procedure is invoked.
   */
  def mark (proc : Val, state : AbstractState) (kont : Kont) : Kont = {
    kont
  }


  /**
   Selects a new abstract context when evaluating the procedure proc.
   */
  def nextContext (proc : Val, state : EvalState) : K ;

  /**
   Selects a new abstract context when evaluating the procedure proc.
   */
  def nextContext (proc : Val, state : EvalAppState) : K ;

  /**
   Selects a new abstract context when applying a procedure.
   */
  def nextContext (state : ApplyProcState) : K ;

  /**
   Selects a new abstract context when moving through an evaluation.
   */
  def nextContext (state : EvalState) : K ;

  /**
   Selects a new abstract context when moving through a conditional branch.
   */
  def nextContext (cond : Boolean, state : EvalState) : K ;

  /**
   Selects a new abstract context when allocating a continuation.
   */
  def nextContext (kont : Kont, state : EvalState) : K ;

  /**
   Selects a new abstract context when applying a continuation.
   */
  def nextContext (state : ApplyKontState) : K ;


  /**
   Selects a new abstract context when applying a primitive operation.
   */
  def nextContext (kont : Kont, state : ApplyProcState) : K ;


  def nextContext (rec : AbstractCommon.Record, kont : Kont, state : EvalState) : K ;




  /**
   Allocates locatives for the supplied variables during procedure application.
   */
  def alloc (vars : List[Var], state : ApplyProcState) : List[Loc] ;

  /**
   Allocates locatives for the supplied variables during evaluation.
   */
  def alloc (vars : List[Var], state : EvalState) : List[Loc] ;

  /*
   Allocates a locative for the freshly allocated continuation.
   */
  def alloc (proc : Val, state : EvalAppState) : Loc ;

  /**
   Allocates a locative for a let binding.
   */
  def alloc (v : Var, state : EvalState) : Loc ;

  /**
   Allocates a locative for a continuation application.
   */
  def alloc (v : Var, state : ApplyKontState) : Loc ; 

  /**
   Allocates a locative for let-induced continuation.
   */
  def alloc (exp : Exp, state : EvalState) : Loc ;

  /**
   Allocates fields for an object.
   */
  def allocNew (kont : Kont, s : EvalState, fields : List[Field], exps : List[Exp]) : (Loc,List[Loc]) ;


  /**
   Determines whether contexts are part of the flat-space or not.
   */
  var cacheContexts = true


  /* Mechanics. */
  private [hofa] case class EvalFlat (val exp : Exp, val bEnv : BEnv, val kontp : Loc, val k : K) extends Flat {
    override lazy val hashCode : Int = 
      (if (cacheContexts) { k.hashCode() * 4 } else 0) + exp.hashCode() * 3 + bEnv.hashCode() *2 + kontp.hashCode()
    override def equals(a : Any) : Boolean = a match {
      case EvalFlat(exp2, bEnv2, kontp2, k2) => (exp equals exp2) && (bEnv equals bEnv2) && (kontp equals kontp2) &&  (!cacheContexts || (k equals k2)) 
      case _ => false
    }
  }

  private [hofa] case class EvalAppFlat (val app : App, val bEnv : BEnv, val kont : Kont, val k : K) extends Flat {
    override lazy val hashCode : Int = 
      (if (cacheContexts) { k.hashCode() *4 } else 0) + app.hashCode() *3 + bEnv.hashCode() *2 + kont.hashCode()
    override def equals(a : Any) : Boolean = a match {
      case EvalFlat(app2, bEnv2, kont2, k2) => (app equals app2) && (bEnv equals bEnv2) && (kont equals kont2) &&  (!cacheContexts || (k equals k2)) 
      case _ => false
    }
  }

  private [hofa] case class ApplyProcFlat (val proc : Val, val dvec : List[D], val kontp : Loc, val k : K) extends Flat {
    private lazy val dvecHashCode = dvec.foldRight (0) (_.hashCode() + 2*_)

    override lazy val hashCode : Int = 
      (if (cacheContexts) { k.hashCode() * 4 } else 0) + proc.hashCode() * 3 + dvecHashCode * 2 + kontp.hashCode()
    override def equals(a : Any) : Boolean = a match {
      case ApplyProcFlat(proc2, dvec2, kontp2, k2) => (proc equals proc) && (dvec.equalsWith(dvec2)(_ equals _)) && (kontp equals kontp2) && (!cacheContexts || (k equals k2))
      case _ => false
    }
  }

  private [hofa] case class ApplyKontFlat (val kont : Kont, val dvec : List[D], val k : K) extends Flat {
    private lazy val dvecHashCode = dvec.foldRight (0) (_.hashCode() + 2*_)

    override lazy val hashCode : Int = 
      (if (cacheContexts) { k.hashCode() * 3 } else 0) + kont.hashCode() * 2 + dvecHashCode 
    override def equals(a : Any) : Boolean = a match {
      case ApplyKontFlat(kont2, dvec2, k2) => (kont equals kont2) && (dvec.equalsWith(dvec2)(_ equals _)) && (!cacheContexts || (k equals k2))
      case _ => false
    }
  }


  
  case class EvalState(val exp : Exp, val bEnv : BEnv, val store : Store, val kontp : Loc, val k : K) extends AbstractState {
    val isCacheable = true
    val isGarbageCollectable = true 

    def flat : Flat = EvalFlat(exp,bEnv,kontp,k)
    
    def store_= (store_ : Store) : EvalState = EvalState(exp,bEnv,store_,kontp,k)

    def sharp : Sharp = Sharp(store)
    def sharp_= (s : Sharp) : EvalState = EvalState(exp,bEnv,s.store,kontp,k)

    override def touches : List[StoreNode] =
      if (useRangeBasedTouching)
        (kontp :: (bEnv.toMap.toList map (_._2))) map (LocNode(_))
      else
        // Free-based GC.
        (LocNode(kontp) :: (exp.freeVars.toList map ((v : Var) => LocNode(bEnv(v)))))

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      F("EvalState",List(O(Map("exp" -> exp.toJSON(),
                               "bEnv" -> bEnv.toJSON(),
                               "store" -> store.toJSON(),
                               "kontp" -> kontp.toJSON(),
                               "k" -> k.toJSON()))))
    }
  }

  case class EvalAppState(val app : App, val bEnv : BEnv, val store : Store, val kont : Kont, val k : K) extends AbstractState {
    val isCacheable = false
    val isGarbageCollectable = false

    def flat : Flat = EvalAppFlat(app,bEnv,kont,k)

    def store_= (store_ : Store) : EvalAppState = EvalAppState(app,bEnv,store_,kont,k)

    def sharp : Sharp = Sharp(store)
    def sharp_= (s : Sharp) : EvalAppState = EvalAppState(app,bEnv,s.store,kont,k)

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      F("EvalState",List(O(Map("app" -> app.toJSON(),
                               "bEnv" -> bEnv.toJSON(),
                               "store" -> store.toJSON(),
                               "kont" -> kont.toJSON(),
                               "k" -> k.toJSON()))))
    }
  }

  case class ApplyProcState(val proc : Val, val dvec : List[D], val store : Store, val kontp : Loc, val k : K) extends AbstractState {
    val isCacheable = false
    val isGarbageCollectable = false

    def flat : Flat = ApplyProcFlat(proc,dvec,kontp,k)

    def store_= (store_ : Store) : ApplyProcState = ApplyProcState(proc,dvec,store_,kontp,k)

    def sharp : Sharp = Sharp(store)
    def sharp_= (s : Sharp) : ApplyProcState = ApplyProcState(proc,dvec,s.store,kontp,k)

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      F("ApplyProcState",List(O(Map("proc" -> proc.toJSON(),
                                    "dvec" -> JSON.fromIterable(dvec),
                                    "store" -> store.toJSON(),
                                    "kontp" -> kontp.toJSON(),
                                    "k" -> k.toJSON()))))
    }
  }

  case class ApplyKontState(val kont : Kont, val dvec : List[D], val store : Store, val k : K) extends AbstractState {
    val isCacheable = false
    val isGarbageCollectable = false

    def flat : Flat = ApplyKontFlat(kont,dvec,k)

    def store_= (store_ : Store) : ApplyKontState = ApplyKontState(kont,dvec,store_,k)

    def sharp : Sharp = Sharp(store)
    def sharp_= (s : Sharp) : ApplyKontState = ApplyKontState(kont,dvec,s.store,k)

    override def toJSON() : JSONExp = {
      import JSONSyntax._ ;
      F("ApplyKontState",List(O(Map("kont" -> kont.toJSON(),
                                    "dvec" -> JSON.fromIterable(dvec),
                                    "store" -> store.toJSON(),
                                    "k" -> k.toJSON()))))
    }
  }


  /**
   AtomExp pattern matches atomic expressions.
   */
  private [hofa] object AtomExp {
    def unapply(exp : Exp) : Option[Unit] = exp match {
      case _ : TrivialExp => Some()
      case App(_ : PPrimOp,_) => Some()
      case _ => None
    }
  }


  /* Satisfying MonotoneTransitionSystem requirements. */
  type C = ListSharpCache[S]

  protected def makeC(init : S) = new ListSharpCache[S](wideningDegree == PerFlatWidening)

  def fuse (flat : F, sharp : S) : N = flat match {
    case EvalFlat(exp,bEnv,kontp,k) => EvalState(exp, bEnv, sharp.store, kontp, k)
    case ApplyProcFlat(proc,dvec,kontp,k) => ApplyProcState(proc,dvec,sharp.store,kontp,k)
  }

  def succ(state : N) : List[N] = state match {

    case s @ EvalState(App(f,args),be,store,kontp,k) => {
      val argVals = args map (atomEval (be,store) _)
      for (proc <- (atomEval (be,store) (f)).toList if proc.isInstanceOf[Proc]) yield {
        val k_ = nextContext(proc,s)
        // BUG/TODO: Enable marking of tail calls.
        /*
        val store_ = if (kontMarkingEnabled) {
          val konts = store(kontp).toList.asInstanceOf[List[Kont]]
          val konts_ = konts map (mark (proc.asInstanceOf[Proc],s) _)
          store.strongUpdate(kontp,mkD(konts_))
        } else {
          store
        }
        */
        val store_ = store
        ApplyProcState(proc, argVals, store_, kontp, k_)
      }
    }

    case s @ EvalState(Let1(v,atom @ AtomExp(()),body),bEnv,store,kontp,k) => {
      val result = atomEval (bEnv,store) (atom)
      val loc = alloc(v,s) 
      val bEnv_ = bEnv + (v,loc)
      val store_ = store + (loc,result)
      val k_ = nextContext(s)
      List(EvalState(body,bEnv_,store_,kontp,k_))
    }

    case s @ EvalState(GetField(rec,field),bEnv,store,kontp,k) => {
      val recs = atomEval (bEnv,store) (rec)
      // TODO: Add flag for merging all objects.
      val states = for (rec <- recs.toList if rec.isInstanceOf[AbstractCommon.Record]) yield {
        val rek = rec.asInstanceOf[AbstractCommon.Record]
        for (kont <- store(kontp).toList if kont.isInstanceOf[Kont]) yield {
          val cont = kont.asInstanceOf[Kont]
          val k_ = nextContext(rek,cont,s) 
          val fieldLoc = rek.fields(field)
          val value = store(fieldLoc)
          ApplyKontState(cont,List(value),store,k_)
        }
      }
      states.foldRight (List[AbstractState]()) ((x : List[AbstractState], y : List[AbstractState]) => x ++ y)
    }
    
    case s @ EvalState(atom @ AtomExp(()),bEnv,store,kontp,k) => {
      val result = atomEval (bEnv,store) (atom)
      for (kont <- store(kontp).toList if kont.isInstanceOf[Kont]) yield {
        val cont = kont.asInstanceOf[Kont]
        val k_ = nextContext(cont,s)
        ApplyKontState(cont, List(result), store, k_)
      }
    }

    case s @ EvalState(LambdoSyntax.Record(fields,exps),bEnv,store,kontp,k) => {
      val vals = exps map (atomEval (bEnv,store))
      for (kont <- store(kontp).toList if kont.isInstanceOf[Kont]) yield {
        val cont = kont.asInstanceOf[Kont]
        val k_ = nextContext(kont,s)
        val (oLoc,fieldLocs) = allocNew(cont,s,fields,exps)
        val fieldsMap = scala.collection.immutable.TreeMap[Field,Loc]() ++ (fields zip fieldLocs)
        val rec = AbstractCommon.Record(oLoc,fieldsMap)
        val store_ = store ++ (fieldLocs zip vals)
        val d = mkD(rec)
        ApplyKontState(cont, List(d), store_, k_)
      }

    }

    case s @ EvalState(Let1(v,app : App,body),bEnv,store,kontp,k_) => {
      val k_ = nextContext(s)
      List(EvalAppState(app,bEnv,store,KontLet1(v,body,bEnv,kontp,initMark),k_))
    }
    
    case s @ EvalState(Let1(v,exp,body),bEnv,store,kontp,k) => {
      val kont = KontLet1(v,body,bEnv,kontp,initMark)
      val kontp_ = alloc(exp,s)
      val store_ = store + (kontp_,mkD(kont))
      val k_ = nextContext(s)
      List(EvalState(exp,bEnv,store_,kontp_,k_))
    }

    case s @ EvalAppState(App(f,args),be,store,kont,k) => {
      val argVals = args map (atomEval (be,store) _)
      for (proc <- (atomEval (be,store) (f)).toList if proc.isInstanceOf[Proc]) yield {
        val k_ = nextContext(proc,s)
        val kont_ = if (kontMarkingEnabled) {
          mark (proc.asInstanceOf[Proc],s) (kont)
        } else {
          kont
        }
        val kontp = alloc(proc,s)
        val store_ = store + (kontp, mkD(kont_))
        ApplyProcState(proc, argVals, store_, kontp, k_)
      }
    }

    case s @ EvalState(If(cond,ifTrue,ifFalse),bEnv,store,kontp,k) => {
      val condd = atomEval (bEnv,store) (cond)
      val kTrue = nextContext(true,s)
      val kFalse = nextContext(false,s)

      if (mustBeTrue(condd)) {
        List(EvalState(ifTrue,bEnv,store,kontp,kTrue))
      } else if (mustBeFalse(condd)) {
        List(EvalState(ifFalse,bEnv,store,kontp,kFalse))
      } else {
        List(EvalState(ifTrue,bEnv,store,kontp,kTrue),
             EvalState(ifFalse,bEnv,store,kontp,kFalse))
      }
    }

    case s @ EvalState(Set(v,e,body),bEnv,store,kontp,k) => {
      val k_ = nextContext(s)
      val argVal = atomEval (bEnv,store) (e)
      val addr = bEnv(v)
      val store_ = (store(addr) = argVal) // strongUpdate if possible.
      List(EvalState(body,bEnv,store_,kontp,k_))
    }

    case s @ EvalState(LetRec(vars,lams,body),bEnv,store,kontp,k) => {
      val k_ = nextContext(s)
      
      val addrs = alloc(vars,s)
      val varsXaddrs = vars zip addrs
      val bEnv_ = bEnv ++ varsXaddrs
      val cloVals = lams map (atomEval (bEnv_,store))
      
      val addrsXvals = addrs zip cloVals
      val store_ = store ++ addrsXvals

      List(EvalState(body,bEnv_,store_,kontp,k_))
    }

    case s @ ApplyProcState(Clo(Lambda(vars,body),bEnv), argVals, store, kontp, k) if vars.length == argVals.length => {
      val k_ = nextContext(s)

      val addrs = alloc(vars,s)

      val varsXaddrs = vars zip addrs
      val addrsXvals = addrs zip argVals
      
      val bEnv_ = bEnv ++ varsXaddrs
      val store_ = store ++ addrsXvals

      List(EvalState(body,bEnv_,store_, kontp, k_))
    }

    case s @ ApplyProcState(Clo(Lambda(vars,body),bEnv), argVals, store, kontp, k) if vars.length != argVals.length => 
      List()

    case s @ ApplyProcState(Op(prim : PPrimOp),argVals,store,kontp,k) => {
      for (cont <- store(kontp).toList if cont.isInstanceOf[Kont]) yield {
        val kont = cont.asInstanceOf[Kont]
        val k_ = nextContext(kont,s)
        val result = primEval (prim.asInstanceOf[PPrimOp], argVals)
        ApplyKontState(kont,List(result),store,k_)
      }
    }
      

    case ApplyProcState(Op(EPrimOp("halt")),_,_,_,_) => List()

    case s @ ApplyProcState(Op(EPrimOp("display" | "newline")),dvec,store,kontp,k) => {
      for (kont <- store(kontp).toList) yield {
        val cont = kont.asInstanceOf[Kont]
        val k_ = nextContext(cont,s)
        ApplyKontState(cont,List(mkD(VoidVal)),store,k_)
      }
    }


    case s @ ApplyKontState(KontLet1(v,exp,bEnv,kontp,mark), List(result), store, k) => {
      val loc = alloc(v,s)
      val bEnv_ = bEnv + (v,loc)
      val store_ = store + (loc,result)
      val k_ = nextContext(s)
      List(EvalState(exp,bEnv_,store_,kontp,k_))
    }

    case s @ ApplyKontState(HaltKont(mark), answers, store, k) => 
      List()

    case unmatched => {
      throw new Exception("Code incomplete; state unmatched:\n " + unmatched)
    }
  }




}




trait UniversalCFA


trait Registerable {
  def serial : Long ;
}



trait DependenceAnalysis extends UniversalCFA_ANF {
  
  import AbstractCommon._
  import LambdoSyntax._

  type N <: AbstractState

  val accesses = scala.collection.mutable.HashMap[ProcCall,scala.collection.mutable.HashSet[Loc]]()
  val modifies = scala.collection.mutable.HashMap[ProcCall,scala.collection.mutable.HashSet[Loc]]()

  private def addrsIn (bEnv : BEnv) (exps : List[Exp]) : List[Loc] = {
    for (e <- exps if e.isInstanceOf[Ref]) yield {
      bEnv(e.asInstanceOf[Ref].v)
    }
  }



  private def reads (state : AbstractState) : List[Loc] = {
    state match {
      case EvalState(a @ AtomExp(()),bEnv,store,kontp,k) => addrsIn (bEnv) (List(a))

      case EvalState(App(f,args),bEnv,store,kontp,k) => addrsIn (bEnv) (f :: args)
      case EvalAppState(App(f,args),bEnv,store,kontp,k) => addrsIn (bEnv) (f :: args)
      case EvalState(Let1(v,e,body),bEnv,store,kontp,k) => addrsIn (bEnv) (List(e))
      case EvalState(LetRec(vars,lams,body),bEnv,store,kontp,k) => List() // LetRec uses nothing.
      case EvalState(If(cond,ifTrue,ifFalse),bEnv,store,kontp,k) => addrsIn (bEnv) (List(cond))
      case EvalState(Set(v,e,body),bEnv,store,kontp,k) => addrsIn (bEnv) (List(e))

      case ApplyProcState(proc,args,store,kontp,k) => List()
      case ApplyKontState(kont,rv,store,k) => List()
    }
  }
  
  private def writes (state : AbstractState) : List[Loc] = {
    state match {
      case EvalState(Set(v,e,body),bEnv,store,kontp,k) => addrsIn(bEnv)(List(e))
      case _ => List()
    }
  }

  private def frames (state : AbstractState) : List[Kont] = {
    val stackGraph = new StackGraph(state.store)

    val konts = state match {
      case EvalState(_,_,store,kontp,_) => store(kontp).toList.asInstanceOf[List[Kont]]
      case EvalAppState(_,_,_,kont,_) => List(kont)
      case ApplyProcState(_,_,store,kontp,_) => store(kontp).toList.asInstanceOf[List[Kont]]
      case ApplyKontState(kont,_,_,_) => List(kont)
    }

    stackGraph.explore(konts)

    stackGraph.seen.toList
  }

  
  def access(call : ProcCall) : scala.collection.mutable.HashSet[Loc] = {
    (accesses get call) match {
      case None => {
        val set : scala.collection.mutable.HashSet[Loc] = new scala.collection.mutable.HashSet[Loc]()
        accesses(call) = set
        set
      }
      case Some(set) => set
    }
  }


  def modify(call : ProcCall) : scala.collection.mutable.HashSet[Loc] = {
    (modifies get call) match {
      case None => {
        val set : scala.collection.mutable.HashSet[Loc] = new scala.collection.mutable.HashSet[Loc]()
        modifies(call) = set
        set
      }
      case Some(set) => set
    }
  }
  

  override def recordTransition(state : N, next : List[N]) {

    // What's on live on the stack?
    val konts = frames(state)

    // What's read here?
    val rs = reads(state)

    // What's written here?
    val ws = writes(state)

    for (kont <- konts) {
      val mark = kont.mark
      val calls = mark.asInstanceOf[CallMark].calls
      
      for (call <- calls) {
        for (r <- rs) {
          val set = access(call)  
          set += r
        }
        
        for (w <- ws) {
          val set = modify(call)
          set += w
        }
      }
    }

    super.recordTransition(state,next)
  }

  private def quote(s : String) : String = {
    s.replaceAll("\\\"","\\\\\"")
  }

  def toDepDot() : String = {
    val s = new StringBuilder() 
    s.append("digraph {\n")
    
    s.append(" graph [rankdir=TB]\n")

    for ((call,locs) <- accesses) {
      for (loc <- locs) {
        val callStr = "\"" + quote(call.toString()) + "\""
        val locStr = "\"" + quote(loc.toJSON().toString()) + "\""
        s.append(" " +locStr+ " -> " +callStr+ "\n")
      }
    }

    for ((call,locs) <- modifies) {
      for (loc <- locs) {
        val callStr = "\"" + quote(call.toString()) + "\""
        val locStr = "\"" + quote(loc.toJSON().toString()) + "\""
        s.append(" " +callStr+ " -> " +locStr+ "\n")
      }
    }

    s.append("}\n")
    s.toString()
  }
}



/**
 A GraphingTransitionSystem constructs a graph of the system during exploration.
 */
trait GraphingTransitionSystem extends TransitionSystem {

  type N <: Registerable

  val narrowingEdges = scala.collection.mutable.HashMap[N,N]()
  val wideningEdges = scala.collection.mutable.HashMap[N,N]()
  val transitionEdges = scala.collection.mutable.HashMap[N,List[N]]()
  val representationEdges = scala.collection.mutable.HashMap[N,N]()

  val index = scala.collection.mutable.HashMap[Long,N]()
  
  override def recordTransition(state : N, next : List[N]) {
    index(state.serial) = state 
    transitionEdges(state) = next
    super.recordTransition(state,next)
  }

  override def recordWidening(state : N, state_ : N) {
    index(state.serial) = state
    if (state.serial == state_.serial) 
      return ;
    wideningEdges(state) = state_
    super.recordWidening(state,state_)
  }

  override def recordNarrowing(state : N, state_ : N) {
    index(state.serial) = state 
    if (state.serial == state_.serial) 
      return ;
    narrowingEdges(state) = state_
    super.recordNarrowing(state,state_)
  }

  override def recordRepresentation(state : N, state_ : N) {
    index(state.serial) = state 
    representationEdges(state) = state_
    super.recordRepresentation(state,state_)
  }


  /**
   Generates a DOT formatted representation of this transition system.
   */
  def toDot() : String = {
    val s = new StringBuilder() 
    s.append("digraph {\n")
    
    s.append(" graph [rankdir=LR]\n") 

    for ((n,succs) <- transitionEdges) {
      for (succ <- succs) {
        s.append(" s" + n.serial + " -> s" + succ.serial + "\n")
      }
    }
    for ((n1,n2) <- representationEdges) {
      s.append(" s" + n1.serial + " -> s" + n2.serial + " [style=dotted]\n")
    }
    for ((n1,n2) <- wideningEdges) {
      s.append(" s" + n1.serial + " -> s" + n2.serial + " [style=dashed]\n")
    }
    for ((n1,n2) <- narrowingEdges) {
      // TODO: Distinguish these edges from widening.
      s.append(" s" + n1.serial + " -> s" + n2.serial + " [style=dashed]\n")
    }
    s.append("}\n")
    s.toString()
  }


  /**
   Renders the graph structure to a JSON object.
   */
  def toJSON() : JSONExp = {
    import JSONSyntax._
    
    var idx = scala.collection.immutable.TreeMap[String,JSONExp]()

    for ((k,v) <- index) {
      idx = (idx(k.toString()) = v.asInstanceOf[JSONable].toJSON())
    }

    O(Map(
      "index" -> O(idx)
    ))
  }
}









class `0CFA_ANF` extends UniversalCFA_ANF {

  import LambdoSyntax._
  import AbstractCommon._

  var useMonoBindingEnvironment = false
  var useHashingStore = true

  def botBEnv = if (useMonoBindingEnvironment) { StandardDomains.MonoBEnv } else { StandardDomains.botBEnv }
  def botStore = if (useHashingStore) { HashingDomains.botStore } else { StandardDomains.botStore }
  def botD = StandardDomains.botD

  def initMark = EmptyCallMark
  
  override def mark (proc : Val, state : AbstractState) (kont : Kont) : Kont = {
    proc match {
      case Clo(lam,be) => kont.mark = (kont.mark.asInstanceOf[CallMark] + MonoProcCall(lam))
      case _ => kont
    }
  }


  type K = AbstractCommon.Context


  def alloc (vars : List[Var], state : ApplyProcState) : List[Loc] =
    vars map (VarLoc(_))
  def alloc (vars : List[Var], state : EvalState) : List[Loc] =
    vars map (VarLoc(_))
  def alloc (v : Var, state : EvalState) : Loc =
    VarLoc(v)
  def alloc (proc : Val, state : EvalAppState) : Loc = proc match {
    case Clo(lam,bEnv) => ExpLoc(lam)
    case Op(prim) => ExpLoc(prim)
  }
  def alloc (exp : Exp, state : EvalState) : Loc = ExpLoc(exp)
  def alloc (v : Var, state : ApplyKontState) : Loc = VarLoc(v)

  def allocNew (kont : Kont, s : EvalState, fields : List[Field], exps : List[Exp]) : (Loc,List[Loc]) = {
    // TODO: Parameterize this.
    val oloc = ExpLoc(s.exp)
    val fieldLocs = fields map (FieldLoc(_,oloc))
    (oloc,fieldLocs)
  }



  def nextContext (s : ApplyProcState) = AbstractCommon.MonoContext
  def nextContext (kont : Kont, s : ApplyProcState) = AbstractCommon.MonoContext
  def nextContext (proc : Val, s : EvalState) = AbstractCommon.MonoContext
  def nextContext (s : EvalState) = AbstractCommon.MonoContext
  def nextContext (cond : Boolean, s : EvalState) = AbstractCommon.MonoContext
  def nextContext (proc : Val, state : EvalAppState) = AbstractCommon.MonoContext
  def nextContext (kont : Kont, state : EvalState) = AbstractCommon.MonoContext
  def nextContext (state : ApplyKontState) = AbstractCommon.MonoContext
  def nextContext (rec : AbstractCommon.Record, kont : Kont, state : EvalState) = AbstractCommon.MonoContext



  def explore (exp : Exp) {
    val store0 = botStore + (HaltLoc,mkD(HaltKont(initMark)))

    val initState = EvalState(exp,botBEnv,store0,HaltLoc,AbstractCommon.MonoContext)
    explore(List(initState))
  }

  override def recordTransition(state : N, next : List[N]) {
    if (steps % 100 == 0) {
      println("steps: " + steps)
    }
    super.recordTransition(state,next)
  }

}




/**
 An implementation of the <b>concrete interpreter</b> as a static analysis, based on the notion of Galois unions.
 */
class Concrete_ANF extends UniversalCFA_ANF {

  import LambdoSyntax._
  import AbstractCommon._


  def botBEnv = StandardDomains.botBEnv
  def botStore = StandardDomains.botStore
  def botD = StandardDomains.botD

  def initMark = EmptyCallMark
  
  override def mark (proc : Val, state : AbstractState) (kont : Kont) : Kont = {
    proc match {
      case Clo(lam,be) => kont.mark = (kont.mark.asInstanceOf[CallMark] + MonoProcCall(lam))
      case _ => kont
    }
  }

  type K = AbstractCommon.Context

  private var maxLoc = 0

  private def alloc() : Loc = {
    maxLoc = maxLoc + 1
    NatLoc(maxLoc)
  }


  def alloc (vars : List[Var], state : ApplyProcState) : List[Loc] =
    vars map (_ => alloc())
  def alloc (vars : List[Var], state : EvalState) : List[Loc] =
    vars map (_ => alloc())
  def alloc (v : Var, state : EvalState) : Loc =
    alloc()
  def alloc (proc : Val, state : EvalAppState) : Loc = proc match {
    case Clo(lam,bEnv) => alloc()
    case Op(prim) => alloc()
  }
  def alloc (exp : Exp, state : EvalState) : Loc = 
    alloc()
  def alloc (v : Var, state : ApplyKontState) : Loc = 
    alloc()

  def allocNew (kont : Kont, s : EvalState, fields : List[Field], exps : List[Exp]) : (Loc,List[Loc]) = {
    // TODO: Parameterize this.
    val oloc = alloc()
    val fieldLocs = fields map (FieldLoc(_,oloc))
    (oloc,fieldLocs)
  }


  def nextContext (s : ApplyProcState) = AbstractCommon.MonoContext
  def nextContext (kont : Kont, s : ApplyProcState) = AbstractCommon.MonoContext
  def nextContext (proc : Val, s : EvalState) = AbstractCommon.MonoContext
  def nextContext (s : EvalState) = AbstractCommon.MonoContext
  def nextContext (cond : Boolean, s : EvalState) = AbstractCommon.MonoContext
  def nextContext (proc : Val, state : EvalAppState) = AbstractCommon.MonoContext
  def nextContext (kont : Kont, state : EvalState) = AbstractCommon.MonoContext
  def nextContext (state : ApplyKontState) = AbstractCommon.MonoContext
  def nextContext (rec : AbstractCommon.Record, kont : Kont, state : EvalState) = AbstractCommon.MonoContext


  /**
   Evaluates a literal expression exactly.
   */
  override def litEval (exp : LitExp) : D = exp match {
    case IntLit(z) => mkD(ExactInt(z))
    case VoidLit() => mkD(VoidVal)
    case BoolLit(true) => mkD(TrueVal)
    case BoolLit(false) => mkD(FalseVal)
    case NilLit() => mkD(NilVal)
    case TextLit(_) => mkD(StringVal)
  }


  private val randomNumberGenerator = new java.util.Random

  /**
   Evaluates a primitive operation exactly.
   */
  override def primEval (p : PPrimOp, argVals : List[D]) : D = (p,argVals) match {
    case (PPrimOp("+"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 + z2))
    case (PPrimOp("-"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 - z2))
    case (PPrimOp("*"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 * z2))
    case (PPrimOp("/"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 / z2))
    case (PPrimOp("="),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 equals z2)
    case (PPrimOp("<"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 < z2)
    case (PPrimOp("<="),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 <= z2)
    case (PPrimOp(">"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(z1 > z2)
    case (PPrimOp("modulo"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 mod z2))
    case (PPrimOp("quotient"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1 / z2))
    case (PPrimOp("gcd"),List(DSingle(ExactInt(z1)),DSingle(ExactInt(z2)))) => mkD(ExactInt(z1.gcd(z2)))
    case (PPrimOp("random-range"),List(DSingle(ExactInt(lo)),DSingle(ExactInt(hi)))) =>
      mkD(ExactInt((BigDecimal(hi-lo) * BigDecimal(Math.random) + BigDecimal(lo)).toBigInt))
    case (PPrimOp("random-byte"),List()) => mkD(ExactInt(randomNumberGenerator.nextInt().abs % 256))
    case (PPrimOp("not"),List(DSingle(FalseVal))) => mkD(TrueVal)
    case (PPrimOp("not"),List(DSingle(_))) => mkD(FalseVal)
    case (PPrimOp("odd?"),List(DSingle(ExactInt(z)))) => mkD((z mod 2) == 1)
    case (PPrimOp("even?"),List(DSingle(ExactInt(z)))) => mkD((z mod 2) == 0)

    case _ => throw new Exception("unknown primop: " + p + ", with arguments: " + argVals)
  }

  

  def explore (exp : Exp) {
    val store0 = botStore + (HaltLoc,mkD(HaltKont(initMark)))

    val initState = EvalState(exp,botBEnv,store0,HaltLoc,AbstractCommon.MonoContext)
    explore(List(initState))
  }


  override def mark(state : N) {} // Don't store states.
  override def seen(state : N) : Option[N] = None // Don't check for states.
  override def widen(state : N) : N = state // Don't widen states.
  override def narrow(state : N) : N = state // Don't narrow states.

  override def recordTransition(state : N, next : List[N]) {
    
    // println("\nsteps: " + steps)
    // println("state: " + state)  

    state match {
      case s @ ApplyKontState(HaltKont(mark), answers, store, k) => {
        println(answers)
      }
      case _ => {}
    }

    super.recordTransition(state,next)
  }

}







/**
 The HOFA object contains a high-level interface to the higher-order flow analysis engine.
 */
object HOFA {

  var sanityChecking = false

  trait Analysis
  case object DependenceAnalysis extends Analysis
  case object ControlFlowAnalysis extends Analysis
  case object ConcreteAnalysis extends Analysis

  private var analyses : List[Analysis] = List()
  private var files : List[String] = List() 

  private var useRangeBasedTouching = true
  private var useAbstractGarbageCollection = true
  private var wideningDegree : WideningDegree = NoWidening
  private var useBindingEnvironmentRestriction = true
  private var useMonoBindingEnvironment = false
  private var useHashingStore = true

  private def parseOptions (args : List[String]) : Unit = args match {
    case "--gc" :: gcOptions :: rest => {
      val gcOps = gcOptions.split(",")
      this.useAbstractGarbageCollection = !gcOps.contains("off")
      this.useRangeBasedTouching = !gcOps.contains("touch=free")

      parseOptions(rest)
    }

    case "--concrete" :: rest => {
      analyses = ConcreteAnalysis :: analyses ;
      parseOptions(rest) 
    }
    case "--deps" :: rest => {
      analyses = DependenceAnalysis :: analyses ;
      parseOptions(rest) 
    }

    case "--widen" :: "perflat" :: rest => {
      wideningDegree = PerFlatWidening ; 
      parseOptions(rest) 
    }

    case "--benv" :: "mono" :: rest => {
      this.useMonoBindingEnvironment = true ;
      parseOptions(rest) 
    }
    case "--store" :: "hash" :: rest => {
      this.useHashingStore = true ;
      parseOptions(rest) 
    }
    case "--store" :: "map" :: rest => { 
      this.useHashingStore = false ; 
      parseOptions(rest) 
    }

    case file :: rest => { 
      files = file :: files ; 
      parseOptions(rest) 
    }

    case Nil => { files = files reverse }
  }

  def main (args : Array[String]) {
    
    // This whole class needs major clean-up.  We need a good
    // architecture for sorting through all of the possible
    // parameters.  Right now, it's all ad-hoc.

    val argList = args.toList

    println("args: " + argList)

    parseOptions(argList)

    println("files: " + files)

    if (analyses isEmpty) {
      analyses = List(ControlFlowAnalysis)
    }

    // BUG/TODO: Support more than one source file.
    val fileName = files(0)
    
    val source = scala.io.Source.fromFile(fileName) mkString ""

    val sparser = new SParser
    val sxs = sparser.parse(source)    

    println("sxs:   " + sxs)

    val defs = sxs map LambdoSyntax.parseDef

    val undefiner = new Undefiner 
    val anfXformer = new ANormalizer
    val cpsXformer = new CPSTransformer
    val untailer = new org.ucombinator.project.lambdo.Untailer

    val dsexp = undefiner(defs)
    println("dsexp: " + dsexp + "\n")

    var exp = dsexp

    if (analyses contains DependenceAnalysis)
      exp = untailer(exp)

    if (true)
      exp = anfXformer(exp)

    // CPS-based CFA:
    if (false) {
      exp = cpsXformer(exp)
      println("cpexp: " + exp)

      val cpcfa = new `0CFA_CPS` with GraphingTransitionSystem
      cpcfa.explore(exp)
      org.ucombinator.io.IO.writeTo("tmp/out.dot",cpcfa.toDot())
      org.ucombinator.io.IO.writeTo("tmp/out.json",cpcfa.toJSON().toString())
    }

    // Use the abstract interpreter as a concrete interpreter:
    if (analyses.contains(ConcreteAnalysis)) {
      val interp = new Concrete_ANF
      interp.explore(exp)
    }


    // Find interprocedural dependences:
    if (analyses.contains(DependenceAnalysis)) {
      val ancfa = new `0CFA_ANF` with GraphingTransitionSystem with DependenceAnalysis
      
      AbstractCommon.useRangeBasedTouching = this.useRangeBasedTouching
      ancfa.wideningDegree = this.wideningDegree
      ancfa.useAbstractGarbageCollection = this.useAbstractGarbageCollection
      ancfa.useBindingEnvironmentRestriction = this.useBindingEnvironmentRestriction
      ancfa.useMonoBindingEnvironment = this.useMonoBindingEnvironment
      ancfa.useHashingStore = this.useHashingStore
      
      System.err.println("touch: " + AbstractCommon.useRangeBasedTouching)
      System.err.println("widen: " + ancfa.wideningDegree)
      System.err.println("gc:    " + ancfa.useAbstractGarbageCollection)
      System.err.println("benvr: " + ancfa.useBindingEnvironmentRestriction)
      System.err.println("monob: " + ancfa.useMonoBindingEnvironment)
      System.err.println()
      
      ancfa.explore(exp)
      println("steps: " + ancfa.steps)
      //println("done!")
      //org.ucombinator.io.IO.writeTo("tmp/out.dot",ancfa.toDot())
      //println("finished: out.dot")
      org.ucombinator.io.IO.writeTo("tmp/dep.dot",ancfa.toDepDot())
      //println("finished: dep.dot")
      //val json = ancfa.toJSON()
      //println("finished: json")
      //val str = json.toString()
      //println("finished: json.toString()")
      //org.ucombinator.io.IO.writeTo("tmp/out.json",str)
      //println("finished: out.json")
    }
      
    ()
  }

}

