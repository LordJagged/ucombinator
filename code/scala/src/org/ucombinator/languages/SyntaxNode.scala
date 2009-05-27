package org.ucombinator.languages ;


/**

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 1.0

 */

private[languages] object SyntaxNode {
  private var maxLabel = 0 ;

  private[languages] def allocateLabel() : Int = {
    var node = -1 ;
    synchronized {
      maxLabel = maxLabel + 1
      node = maxLabel
    }
    node
  }
}



/**

 Every syntax node receives a unique label.
 
 By default, hashing, equality and total ordering are based upon this label.

 A SyntaxNode object is Extensible, so that third-party packages
 (e.g. static analyses) can attach arbitrary properties to a node.
  

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 1.0

 */
trait SyntaxNode extends Ordered[SyntaxNode] with org.ucombinator.lang.Extensible {
  val label = SyntaxNode.allocateLabel()

  override def hashCode() : Int = label
  override def equals (o : Any) : Boolean = o match {
    case (alphaNode : AlphaSyntaxNode) => throw new Exception("Comparing SyntaxNode to AlphaSyntaxNode for equality!?")
    case (node : SyntaxNode) => node.label == this.label
    case _ => false
  }
  override def compare (n : SyntaxNode) : Int = n match {
    case (alphaNode : AlphaSyntaxNode) => throw new Exception("Comparing SyntaxNode to AlphaSyntaxNode!?")
    case (node : SyntaxNode) => this.label compare node.label
  }
}



/**

 An AlphaSyntaxNode is treated identically to other AlphaSyntaxNodes
 with the same internal name with respect to hashing, equality and
 total ordering.

 This sort of behavior is most commonly desired with terms representing variables and references.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 1.0

 */
trait AlphaSyntaxNode extends SyntaxNode {
  val internalName : String ;

  override def hashCode() : Int = internalName.hashCode()
  override def equals (o : Any) : Boolean = o match {
    case (alphaNode : AlphaSyntaxNode) => this.internalName equals alphaNode.internalName
    case (node : SyntaxNode) => throw new Exception("Comparing SyntaxNode to AlphaSyntaxNode for equality!?")
    case _ => false
  }
  override def compare (n : SyntaxNode) : Int = n match {
    case (alphaNode : AlphaSyntaxNode) => this.internalName compare alphaNode.internalName  
    case (node : SyntaxNode) => throw new Exception("Comparing SyntaxNode to AlphaSyntaxNode!?")
  }
}

