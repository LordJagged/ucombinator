package org.ucombinator.project.lambdo ;



/**
 An Undefiner transformation converts a sequence of definitions into a single expression with lets and sets.
 */
class Undefiner {
  import LambdoSyntax._ ;

  def apply(defs : List[Def]) : Exp = {
    val names = defs map (_.name)
    Lets(names, defs map (_ => VoidLit()), 
         Sets(names, defs map (_.rhs), Ref(Var("last"))))
  }
}
