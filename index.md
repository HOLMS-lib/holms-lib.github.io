# A HOL Light Library for Modal Systems

This website gives a brief overview of our [HOLMS library](https://github.com/HOLMS-lib/HOLMS) for the [HOL Light](https://hol-light.github.io/) theorem prover.

## Publications

- Marco Maggesi, Cosimo Perini Brogi (2021)<br/>
  ***A Formal Proof of Modal Completeness for Provability Logic***.<br/>
  In 12th International Conference on Interactive Theorem Proving (ITP 2021).<br/>
  Leibniz International Proceedings in Informatics (LIPIcs),<br/>
  Volume 193, pp. 26:1-26:18, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2021)<br/>
  DOI:[10.4230/LIPIcs.ITP.2021.26](https://doi.org/10.4230/LIPIcs.ITP.2021.26) (Open access)
- Marco Maggesi, Cosimo Perini Brogi (2023)<br/>
  ***Mechanising Gödel–Löb Provability Logic in HOL Light***.<br/>
  J Autom Reasoning 67, 29. DOI:[10.1007/s10817-023-09677-z](https://doi.org/10.1007/s10817-023-09677-z) (Open access)
- Antonella Bilotta, Marco Maggesi, Cosimo Perini Brogi, Leonardo Quartini (2024)<br/>
  ***Growing HOLMS, a HOL Light Library for Modal Systems***.<br/>
  (In preparation)

## Contributors

- Antonella Bilotta, University of Florence, Italy
- [Marco Maggesi](https://sites.google.com/unifi.it/maggesi/), University of Florence, Italy
- [Cosimo Perini Brogi](https://logicosimo-gitlab-io-logicosimo-ad8371f8e99a5e895c64ff5b4f9ba89.gitlab.io/), IMT School for Advanced Studies Lucca, Italy
- Leonardo Quartini, University of Florence, Italy


## Principal definitions and theorems

### Axiomatic Definition
```
let MODPROVES_RULES,MODPROVES_INDUCT,MODPROVES_CASES =
  new_inductive_definition
  `(!H p. KAXIOM p ==> [S . H |~ p]) /\
   (!H p. p IN S ==> [S . H |~ p]) /\
   (!H p. p IN H ==> [S . H |~ p]) /\
   (!H p q. [S . H |~ p --> q] /\ [S . H |~ p] ==> [S . H |~ q]) /\
   (!H p. [S . {} |~ p] ==> [S . H |~ Box p])`;;
```

### Deduction Lemma
```
MODPROVES_DEDUCTION_LEMMA
|- !S H p q. [S . H |~ p --> q] <=> [S . p INSERT H |~ q]
```

### Relational semantics

Kripke's Semantics of formulae.

```
let holds =
  let pth = prove
    (`(!WP. P WP) <=> (!W:W->bool R:W->W->bool. P (W,R))`,
     MATCH_ACCEPT_TAC FORALL_PAIR_THM) in
  (end_itlist CONJ o map (REWRITE_RULE[pth] o GEN_ALL) o CONJUNCTS o
   new_recursive_definition form_RECURSION)
  `(holds WR V False (w:W) <=> F) /\
   (holds WR V True w <=> T) /\
   (holds WR V (Atom s) w <=> V s w) /\
   (holds WR V (Not p) w <=> ~(holds WR V p w)) /\
   (holds WR V (p && q) w <=> holds WR V p w /\ holds WR V q w) /\
   (holds WR V (p || q) w <=> holds WR V p w \/ holds WR V q w) /\
   (holds WR V (p --> q) w <=> holds WR V p w ==> holds WR V q w) /\
   (holds WR V (p <-> q) w <=> holds WR V p w <=> holds WR V q w) /\
   (holds WR V (Box p) w <=>
    !w'. w' IN FST WR /\ SND WR w w' ==> holds WR V p w')`;;

let holds_in = new_definition
  `holds_in (W,R) p <=> !V w:W. w IN W ==> holds (W,R) V p w`;;

let valid = new_definition
  `L |= p <=> !f:(W->bool)#(W->W->bool). f IN L ==> holds_in f p`;;
```

### Soundness and consistency of K
```
K_CONSISTENT
|- ~ [{} . {} |~ False]
```

### Soundness and consistency of GL
```
GL_consistent 
|- ~ [GL_AX . {} |~  False]
```

### Completeness theorem

The proof is organized in three steps.

#### STEP 1
Identification of a non-empty set of possible worlds, given by a subclass of maximal consistent sets of formulas.

Parametric Definitions in gen_completness.ml
```
let FRAME_DEF = new_definition
  `FRAME = {(W:W->bool,R:W->W->bool) | ~(W = {}) /\
                                       (!x y:W. R x y ==> x IN W /\ y IN W)}`;;

let GEN_STANDARD_FRAME_DEF = new_definition
  `GEN_STANDARD_FRAME P S p =
   FRAME INTER P INTER
   {(W,R) | W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))}`;;

let GEN_STANDARD_MODEL_DEF = new_definition
  `GEN_STANDARD_MODEL P S p (W,R) V <=>
   (W,R) IN GEN_STANDARD_FRAME P S p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;
```

Definitions in k_completness.ml
```
let K_FRAME_DEF = new_definition
  `K_FRAME = {(W:W->bool,R) | (W,R) IN FRAME /\ FINITE W}`;;

let K_STANDARD_FRAME_DEF = new_definition
  `K_STANDARD_FRAME = GEN_STANDARD_FRAME K_FRAME {}`;;

IN_K_STANDARD_FRAME
|- `(W,R) IN K_STANDARD_FRAME p <=>
   W = {w | MAXIMAL_CONSISTENT {} p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   (W,R) IN K_FRAME /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`

let K_STANDARD_MODEL_DEF = new_definition
   `K_STANDARD_MODEL = GEN_STANDARD_MODEL K_FRAME {}`;;

K_STANDARD_MODEL_CAR
|- `K_STANDARD_MODEL p (W,R) V <=>
   (W,R) IN K_STANDARD_FRAME p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`
```

Definitions in gl_completness.ml
```
let ITF_DEF = new_definition
  `ITF =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    FINITE W /\
    (!x. x IN W ==> ~R x x) /\
    (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

let GL_STANDARD_FRAME_DEF = new_definition
  `GL_STANDARD_FRAME p = GEN_STANDARD_FRAME ITF GL_AX p`;;

IN_GL_STANDARD_FRAME
|- `!p W R. (W,R) IN GL_STANDARD_FRAME p <=>
           W = {w | MAXIMAL_CONSISTENT GL_AX p w /\
                    (!q. MEM q w ==> q SUBSENTENCE p)} /\
           (W,R) IN ITF /\
           (!q w. Box q SUBFORMULA p /\ w IN W
                  ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`

let GL_STANDARD_MODEL_DEF = new_definition
   `GL_STANDARD_MODEL = GEN_STANDARD_MODEL ITF GL_AX`;;

GL_STANDARD_MODEL_CAR
|- `!W R p V.
     GL_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN GL_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p)) `
```

#### STEP 2
Definition of a “standard” accessibility relation depending on axiom set S between these worlds such that the frame is appropriate to S.

Parametric definition of the standard relation in gen_completness.ml
```
let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;
```

In k_completness.ml
```
let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p = GEN_STANDARD_REL {} p`;;

K_STANDARD_REL_CAR
|-`K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT {} p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT {} p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`

K_ACCESSIBILITY_LEMMA_1
 |- `!p w q.
    ~ [{} . {} |~ p] /\
    MAXIMAL_CONSISTENT {} p w /\
    (!q. MEM q w ==> q SUBSENTENCE p) /\
    Box q SUBFORMULA p /\
    (!x. K_STANDARD_REL p w x ==> MEM q x)
    ==> MEM (Box q) w`
```

In GL
```
let GL_STANDARD_REL_DEF = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

GL_ACCESSIBILITY_LEMMA
|- `!p M w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p M /\
     (!q. MEM q M ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     MEM (Not p) M /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`
```

#### STEP 3
Parametric truth lemma in gen_completness.ml
```
GEN_TRUTH_LEMMA
|- `!P S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL P S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`
```

Completeness of K in k_completness.ml
```
K_COMPLETENESS_THM
|- `!p. K_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`
```

Completeness of GL in gl_completness.ml
```
COMPLETENESS_THEOREM 
|- `!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`
```

### Finite model property and decidability

#### In K
Construction of the countermodels.
```
let K_STDWORLDS_RULES,K_STDWORLDS_INDUCT,K_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT {} p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN K_STDWORLDS p`;;

let K_STDREL_RULES,K_STDREL_INDUCT,K_STDREL_CASES = new_inductive_definition
  `!w1 w2. K_STANDARD_REL p w1 w2
           ==> K_STDREL p (set_of_list w1) (set_of_list w2)`;;
```

Theorem of existence of the finite countermodel.
```
k_COUNTERMODEL_FINITE_SETS
|- `!p. ~[{} . {} |~ p] ==> ~holds_in (K_STDWORLDS p, K_STDREL p) p`
```

#### In GL
Construction of the countermodels.
```
let GL_STDWORLDS_RULES,GL_STDWORLDS_INDUCT,GL_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT GL_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN GL_STDWORLDS p`;;

let GL_STDREL_RULES,GL_STDREL_INDUCT,GL_STDREL_CASES = new_inductive_definition
  `!w1 w2. GL_STANDARD_REL p w1 w2
           ==> GL_STDREL p (set_of_list w1) (set_of_list w2)`;;
```

Theorem of existence of the finite countermodel.
```
GL_COUNTERMODEL_FINITE_SETS
|- `!p. ~ [GL_AX . {} |~ p] ==> ~holds_in (GL_STDWORLDS p, GL_STDREL p) p`
```

### Automated theorem proving and countermodel construction

#### In K

Our tactic `K_TAC` and its associated rule `K_RULE` can automatically prove theorems in the modal logic K.

Examples:
```
K_RULE `!a b. [{} . {} |~ Box (a && b) <-> Box a && Box b]`;;

K_RULE `!a b. [{} . {} |~ Box a || Box b --> Box (a || b)]`;;
```

#### In GL

Our tactic `GL_TAC` and its associated rule `GL_RULE` can automatically prove theorems in the modal logic GL.
Here is a list of examples

#### Example of a formula valid in GL but not in K
```
time GL_RULE
  `!a. [GL_AX . {} |~ Box Diam Box Diam a <-> Box Diam a]`;;
```

#### Formalised Second Incompleteness Theorem
In PA, the following is provable: If PA is consistent, it cannot prove its own consistency.
```
let GL_second_incompleteness_theorem = time GL_RULE
  `[GL_AX . {} |~ Not (Box False) --> Not (Box (Diam True))]`;;
```

#### PA ignores unprovability statements
```
let GL_PA_ignorance = time GL_RULE
  `!p. [GL_AX . {} |~ (Box False) <-> Box (Diam p)]`;;
```

#### PA undecidability of consistency
If PA does not prove its inconsistency, then its consistency is undecidable.
```
let GL_PA_undecidability_of_consistency = time GL_RULE
  `[GL_AX . {} |~ Not (Box (Box False))
                  --> Not (Box (Not (Box False))) &&
                      Not (Box (Not (Not (Box False))))]`;;
```
#### Undecidability of Gödels formula
```
let GL_undecidability_of_Godels_formula = time GL_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) && Not (Box (Box False))
                      --> Not (Box p) && Not (Box (Not p))]`;;
```

#### Reflection and iterated consistency
If a reflection principle implies the second iterated consistency assertion, then the converse implication holds too.
```
let GL_reflection_and_iterated_consistency = time GL_RULE
  `!p. [GL_AX . {} |~ Box ((Box p --> p) --> Diam (Diam True))
                      --> (Diam (Diam True) --> (Box p --> p))]`;;
```

#### A Godel sentence is equiconsistent with a consistency statement
```
let GL_Godel_sentence_equiconsistent_consistency = time GL_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) <->
                      Box (p <-> Not (Box False))]`;;
```

#### Arithmetical fixpoint
For any arithmetical sentences p q, p is equivalent to unprovability of q --> p iff p is equivalent to consistency of q.
```
let GL_arithmetical_fixpoint = time GL_RULE
  `!p q. [GL_AX . {} |~ Dotbox (p <-> Not (Box (q --> p))) <->
                        Dotbox (p <-> Diam q)]`;;
```
