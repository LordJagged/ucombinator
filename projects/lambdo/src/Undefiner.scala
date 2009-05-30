package org.ucombinator.project.lambdo ;



/**
 An Undefiner transformation converts a sequence of definitions into a single expression with lets and sets.

 @author <a href="http://matt.might.net/">Matthew Might</a>
 @version 0.6
 */
class Undefiner {
  import LambdoSyntax._ ;

  private def split (defs : List[Def]) : (List[FunDef],List[VarDef],List[ImpDef]) = {
    if (defs.isEmpty)
      return (List(),List(),List())

    val (funs,vars,imps) = split (defs.tail)
    
    defs.head match {
      case d : FunDef => (d :: funs, vars, imps)
      case d : VarDef => (funs, d :: vars, imps)
      case d : ImpDef => (funs,vars,d :: imps)
    }
  }

  /**
   Performs a lets+sets transform.

   This avoids letrecs.
   */
  private def strictTranform (defs : List[Def]) : Exp = {
    val names = defs map (_.name)
    Lets(names, defs map (_ => VoidLit()), 
         Sets(names, defs map (_.rhs), Ref(Var("last"))))    
  }

  private def nonstrictTransform (defs : List[Def]) : Exp = {
    val (funs,vars,imps) = split(defs)
    

    val varNames = vars map (_.name)
    val varExps = vars map (_.rhs)
    
    val funNames = funs map (_.name)
    val funExps = funs map (_.rhs)

    val impNames = imps map (_.name)
    val impExps = imps map (_.rhs) 

    Lets(Var("last") :: varNames,
         VoidLit() :: varNames map (_ => VoidLit()),
         LetRec(funNames, funExps map (_.asInstanceOf[Lambda]), 
                Sets(varNames, varExps,
                     Sets(impNames, impExps, Ref(Var("last"))))))
             
  }

  def apply(defs : List[Def]) : Exp = {

    defs match {
      // The easy case:
      case List(ImpDef(rhs)) => return rhs
      case _ => {}
    }

    nonstrictTransform(defs)
  }
}
