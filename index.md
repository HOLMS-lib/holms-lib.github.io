# A HOL Light Library for Modal Systems

To be done.

Axiomatic Definition:
```
let MODPROVES_RULES,MODPROVES_INDUCT,MODPROVES_CASES =
  new_inductive_definition
  `(!H p. KAXIOM p ==> [S . H |~ p]) /\
   (!H p. p IN S ==> [S . H |~ p]) /\
   (!H p. p IN H ==> [S . H |~ p]) /\
   (!H p q. [S . H |~ p --> q] /\ [S . H |~ p] ==> [S . H |~ q]) /\
   (!H p. [S . {} |~ p] ==> [S . H |~ Box p])`;;
```
Dedction Lemma:
```
let MODPROVES_DEDUCTION_LEMMA = prove
 (`!S H p q. [S . H |~ p --> q] <=> [S . p INSERT H |~ q]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `[S . p INSERT H |~ q] ==> [S . H |~ p --> q]`
    (fun th -> MESON_TAC[th; MODPROVES_DEDUCTION_LEMMA_INSERT]) THEN
  ASM_CASES_TAC `p:form IN H` THENL
  [SUBGOAL_THEN `p:form INSERT H = H` SUBST1_TAC THENL
   [ASM SET_TAC []; ALL_TAC] THEN
   MESON_TAC[MODPROVES_RULES; MLK_add_assum]; ALL_TAC] THEN
  INTRO_TAC "hp" THEN
  SUBGOAL_THEN `H = (p:form INSERT H) DELETE p` SUBST1_TAC THENL
  [ASM SET_TAC []; ALL_TAC] THEN
  MATCH_MP_TAC MODPROVES_DEDUCTION_LEMMA_DELETE THEN
  ASM_REWRITE_TAC[IN_INSERT]);;
```


Relational semantics
```
(* ------------------------------------------------------------------------- *)
(* Kripke's Semantics of formulae.                                           *)
(* ------------------------------------------------------------------------- *)

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

Soundness and consistency of GL
```
let GL_consistent = prove
 (`~ [GL_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              ITF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```
Soundness and consistency of K
```
g `~ [{} . {} |~ False]`;;
e (REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] K_FRAME_VALID)));;
e (REWRITE_TAC[NOT_IN_EMPTY]);;
e (REWRITE_TAC[valid; holds; holds_in;
               FORALL_PAIR_THM; K_FRAME_CAR; NOT_FORALL_THM]);;
e (MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`]);;
e (REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING]);;
e (MESON_TAC[]);;
let K_CONSISTENT = top_thm ();;;
```
