# A HOL Light Library for Modal Systems

This website gives a brief overview of our [HOLMS library](https://github.com/HOLMS-lib/HOLMS) for the [HOL Light](https://hol-light.github.io/) theorem prover.

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
|- `!S H p q. [S . H |~ p --> q] <=> [S . p INSERT H |~ q]`
```

### Relational semantics

Kripke's Semantics of formulae.

```
let holds =
  let pth = prove
    (`(!WP. P WP) <=> (!W R. P (W,R))`,
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
  `holds_in (W,R) p <=> !V w. w IN W ==> holds (W,R) V p w`;;

parse_as_infix("|=",(11,"right"));;

let valid = new_definition
  `L: (W->bool)#(W->W->bool)->bool |= p <=> !f. L f ==> holds_in f p`;;
```

### Soundness and consistency of GL
```
GL_consistent 
 |- `~ [GL_AX . {} |~  False]`
```
### Soundness and consistency of K
```
K_CONSISTENT
 |- `~ [{} . {} |~ False]`
```

### Completeness theorem
#### STEP 1.
Identification of a non-empty set of possible worlds, given by a subclass of maximal consistent sets of formulas.

Parametric Definitions
```
let GEN_STANDARD_FRAME = new_definition
  `GEN_STANDARD_FRAME K S p (W,R) <=>
   W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   K (W,R)  /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x)) /\
   (K (W,R) ==> FRAME(W,R))`;;

let GEN_STANDARD_MODEL = new_definition
  `GEN_STANDARD_MODEL K S p (W,R) V <=>
   GEN_STANDARD_FRAME K S p (W,R) /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;
```

Definitions in K
```
let K_FRAME = new_definition
 `K_FRAME (W,R) <=> 
  FRAME(W,R) /\ FINITE W`;;

let K_STANDARD_FRAME = new_definition
 `K_STANDARD_FRAME p (W,R) <=>
  GEN_STANDARD_FRAME K_FRAME {} p (W,R)`;;

let K_STANDARD_MODEL = new_definition
   `K_STANDARD_MODEL p (W,R) V <=>
    GEN_STANDARD_MODEL K_FRAME {} p (W,R) V`;;
```

Definitions in GL
```
let ITF = new_definition
  `ITF (W:W->bool,R:W->W->bool) <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> ~R x x) /\
   (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)`;;

let GL_STANDARD_FRAME = new_definition
  `GL_STANDARD_FRAME p (W,R) <=>
   GEN_STANDARD_FRAME ITF GL_AX p (W,R)`;;

let GL_STANDARD_MODEL = new_definition
   `GL_STANDARD_MODEL p (W,R) V <=>
    GEN_STANDARD_MODEL ITF GL_AX p (W,R) V`;;
```



#### STEP 2.
Definition of a “standard” accessibility relation depending on axiom set S between these worlds such that the frame is appropriate to S.

Parametric definition of the standard relation
```
let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;
```

In K
```
let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p w x <=> GEN_STANDARD_REL {} p w x`;;


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
let GL_STANDARD_REL = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

ACCESSIBILITY_LEMMA
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


#### STEP 3.
Parametric truth lemma.
```
GEN_TRUTH_LEMMA
 |- `!K S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL K S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`
```

Completness of K
```
K_COMPLETENESS_THM
 |- `!p. K_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`
```

Completness of GL
```
COMPLETENESS_THEOREM 
 |- `!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`
```
### Finite model property and decidability

### Automated theorem proving and countermodel construction
