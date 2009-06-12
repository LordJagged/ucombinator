*** U Combinator :: Higher-Order Flow Analysis Engine (HOFA) ***

 HOFA aims to be a generic "middle-end" for Scheme, and eventually,
 other functional programming languages. 

 Internally, HOFA consists of a flexible, parameterized abstract
 interpretation.

 Our long-term goal is to provide static analysis data in convenient
 formats, including:

 * Annotated versions of the input program.

 * Raw dumps of the analysis data in:
   - S-Expressions
   - XML
   - SXML 
   - JSON [supported]
   - DOT  [supported]




** Compiling HOFA **

 To compile HOFA, run:

 % make all

 *FROM THE ROOT* of the public U Combinator repository (../../), in
 order to compile all dependencies.



** Running HOFA **

 To run HOFA:

 % sh bin/hofa.run HOFA [flags] <source file>

 Eventually, we'll have documentation for the flags to HOFA.  At them
 moment, you can examine the main() method in HOFA.scala to see what
 they are.

 You may need to modify or uncomment some code to enable some
 analyses.  (Eventually, you won't have to do this.)

 * Concrete interpreter:
 
  You can run force the abstract interpretation to behave like a
  concrete interpreter, which is great for debugging:

  % sh bin/HOFA.run HOFA --concrete --store map <files>


 * Dependence analysis:

  The recommended configuration is:

  % sh bin/HOFA.run HOFA --deps --gc touch=free --benv mono <files>




