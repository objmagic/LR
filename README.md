# LR
explore different techniques to generate LR(k) parsing code

``m41.ml`` -- hand-rolled parsers for ASU grammar 4.1 and 4.55. These
parsers serve as references for how generated code should look like.

``lr_parser.ml`` -- a type-safe LR(1) automata building engine. The idea is
to build automata and interpret it to generate code (or we can generate on-the-fly).

``genf1.ml`` -- some crazy code by Drup. It can be useful.


# Methods

* Normal approach

  * very naive LR(1) parsing algorithm. use hardcoded lr(1) parsing code to interpret array-based table

* Automata simulated by GADT

  * Hardcoded GADT

  * Hardcoded optimized GADT

  * token information --> optional intermediate data structure like a GADT? --> use typed refunctionalization to generate mutually recursive functionals (optimized)
   
  * Generate optimized GADT using MetaOCaml (techinically impossible now)

* Stackless LR(1) parser
  
  * An improvement to [Derivation of a Typed Functional LR Parser](http://www.cs.ox.ac.uk/ralf.hinze/publications/TypedLR.pdf)  
    Stack is implicitly represented as continuation function (CPS). Since no explicit
    stack data structure is present, it is possible to use MetaOCaml to generate
    parser.

    Jeremy, Runhang (01/18/16):  
    maybe can use direct style, which is much easier for us to generate code.
    But if one state has two different reduce production rules, we can't turn
    CPS to direct style. Frederic showed one state can have to different reduction
    rules, so we can't have direct style :(

# How-to

Take a canonical example, Grammar 4.1 in _Aho_.

1. manually go over all algorithms on paper, get very familar with LR(1) parsing process. How optimization works?

2. write naive LR(1) parser on computer

3. try different black technologies
  

