# A HOL Light Library for Modal Systems

This website gives a brief overview of our [HOLMS library](https://github.com/HOLMS-lib/HOLMS) for the [HOL Light](https://hol-light.github.io/) theorem prover.

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
let GL_consistent = prove
 (`~ [GL_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              ITF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```

### Soundness and consistency of K
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


g `!p w q.
    ~ [{} . {} |~ p] /\
    MAXIMAL_CONSISTENT {} p w /\
    (!q. MEM q w ==> q SUBSENTENCE p) /\
    Box q SUBFORMULA p /\
    (!x. K_STANDARD_REL p w x ==> MEM q x)
    ==> MEM (Box q) w`;;
e (REPEAT STRIP_TAC);;
e (REMOVE_THEN "" MP_TAC);;
e (MATCH_MP_TAC EQ_IMP);;
e (MATCH_MP_TAC K_ACCESSIBILITY_LEMMA);;
e (ASM_REWRITE_TAC[]);;
let K_ACCESSIBILITY_LEMMA_1 = top_thm();;
```

In GL
```
let GL_STANDARD_REL = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

let ACCESSIBILITY_LEMMA = prove
 (`!p M w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p M /\
     (!q. MEM q M ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     MEM (Not p) M /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
  REPEAT GEN_TAC THEN INTRO_TAC "p maxM subM maxw subw notp boxq rrr" THEN
  REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "rrr" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN
  CLAIM_TAC "consistent_X"
    `CONSISTENT GL_AX (CONS (Not q) (CONS (Box q)
       (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)))` THENL
  [REMOVE_THEN "contra" MP_TAC THEN REWRITE_TAC[CONSISTENT; CONTRAPOS_THM] THEN
   INTRO_TAC "incons" THEN MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
   MAP_EVERY EXISTS_TAC [`GL_AX`; `p:form`;
     `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MEM_FLATMAP_LEMMA] THEN MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Box(Box q --> q)` THEN
   REWRITE_TAC[GL_axiom_lob] THEN MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC
     `CONJLIST (MAP (Box)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]; ALL_TAC] THEN
   CLAIM_TAC "XIMP"
     `!x y l.
       [GL_AX . {} |~ Not (Not y && CONJLIST (CONS x l))]
        ==> [GL_AX . {} |~ (CONJLIST (MAP (Box) l)) --> Box(x --> y)]` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `Box (CONJLIST l)` THEN CONJ_TAC THENL
    [MESON_TAC[CONJLIST_MAP_BOX;MLK_iff_imp1]; ALL_TAC] THEN
    MATCH_MP_TAC MLK_imp_box THEN MATCH_MP_TAC MLK_shunt THEN
    ONCE_REWRITE_TAC[GSYM MLK_contrapos_eq] THEN MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `CONJLIST (CONS x l) --> False` THEN CONJ_TAC THENL
    [ASM_MESON_TAC[MLK_shunt; MLK_not_def];
     MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Not (CONJLIST(CONS x l))` THEN
     CONJ_TAC THENL
     [MESON_TAC[MLK_axiom_not;MLK_iff_imp2];
      MESON_TAC[MLK_contrapos_eq;CONJLIST_CONS; MLK_and_comm_th;
                MLK_iff_imp2; MLK_iff_imp1; MLK_imp_trans]]];
    ALL_TAC] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   HYP_TAC "incons" (REWRITE_RULE[CONSISTENT]) THEN
   HYP_TAC "incons" (ONCE_REWRITE_RULE[CONJLIST]) THEN
   HYP_TAC "incons" (REWRITE_RULE[NOT_CONS_NIL]) THEN
   POP_ASSUM MATCH_ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC (SPECL
    [`GL_AX`; `p:form`;
     `CONS (Not q) (CONS (Box q)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))`]
    EXTEND_MAXIMAL_CONSISTENT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THENL
   [MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE THEN
    REWRITE_TAC[UNWIND_THM1] THEN HYP MESON_TAC "boxq"
      [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   POP_ASSUM (DESTRUCT_TAC "@y. +" o REWRITE_RULE[MEM_FLATMAP]) THEN
   STRUCT_CASES_TAC (SPEC `y:form` (cases "form")) THEN REWRITE_TAC[MEM] THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THENL
   [MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN
    CLAIM_TAC "rmk" `Box a SUBSENTENCE p` THENL
    [POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []; ALL_TAC] THEN
    HYP_TAC "rmk" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]) THEN
    TRANS_TAC SUBFORMULA_TRANS `Box a` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []];
   ALL_TAC] THEN
  INTRO_TAC "@X. maxX subX subl" THEN EXISTS_TAC `X:form list` THEN
  ASM_REWRITE_TAC[GL_STANDARD_REL_CAR; NOT_IMP] THEN CONJ_TAC THENL
  [CONJ_TAC THENL
   [INTRO_TAC "!B; B" THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
    CONJ_TAC THEN REMOVE_THEN "subl" MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THENL
    [DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN EXISTS_TAC `Box B` THEN
     ASM_REWRITE_TAC[MEM];
     DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN
     EXISTS_TAC `Box B` THEN ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
   EXISTS_TAC `q:form` THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
   CONJ_TAC THENL
   [REMOVE_THEN "subl" MATCH_MP_TAC THEN REWRITE_TAC[MEM]; ALL_TAC] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT];
   ALL_TAC] THEN
  HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]) THEN
  REWRITE_TAC[MEM] THEN
  IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT] THEN
  SIMP_TAC[] THEN INTRO_TAC "_" THEN MATCH_MP_TAC SUBFORMULA_TRANS THEN
  EXISTS_TAC `Box q` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]) ;;
```


#### STEP 3.
Parametric truth lemma.
```
let GEN_TRUTH_LEMMA = prove
 (`!K S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL K S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GEN_STANDARD_MODEL; GEN_STANDARD_FRAME; SUBSENTENCE_CASES] THEN
  INTRO_TAC "np ((W K 1 2) val) q" THEN REMOVE_THEN "W" SUBST_VAR_TAC THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REMOVE_THEN "q" MP_TAC THEN
  HYP_TAC "1" (REWRITE_RULE[IN_ELIM_THM]) THEN
  HYP_TAC "val" (REWRITE_RULE[FORALL_IN_GSPEC]) THEN
  SPEC_TAC (`q:form`,`q:form`) THEN MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[holds] THEN
  CONJ_TAC THENL
  [INTRO_TAC "sub; !w; w" THEN
   HYP_TAC "w -> cons memq" (REWRITE_RULE[MAXIMAL_CONSISTENT]) THEN
   ASM_MESON_TAC[FALSE_IMP_NOT_CONSISTENT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[MAXIMAL_CONSISTENT] THEN
   INTRO_TAC "p; !w; (cons (norep mem)) subf" THEN
   HYP_TAC "mem: t | nt" (C MATCH_MP (ASSUME `True SUBFORMULA p`)) THEN
   ASM_REWRITE_TAC[] THEN
   REFUTE_THEN (K ALL_TAC) THEN
   REMOVE_THEN "cons" MP_TAC THEN REWRITE_TAC[CONSISTENT] THEN
   REWRITE_TAC[MLK_not_def] THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `Not True` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN
   MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_ACCEPT_TAC MLK_not_true_th;
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![q/a]; q; sub; !w; w" THEN REMOVE_THEN "q" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub1 q"] THEN EQ_TAC THENL
    [HYP MESON_TAC "w sub1 q" [MAXIMAL_CONSISTENT_MEM_NOT];
     REMOVE_THEN "q" (MP_TAC o SPEC `w: form list`) THEN
     ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]];
     ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY
  (INTRO_TAC "![q1] [q2]; q1 q2; sub; !w; w" THEN
   REMOVE_THEN "q1" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub1 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
   REMOVE_THEN "q2" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub2 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
   HYP REWRITE_TAC "w" [] THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   CLAIM_TAC "rmk"
     `!q. q SUBFORMULA p ==> (MEM q w <=> [S. {} |~ CONJLIST w --> q])` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
    ALL_TAC]) THENL [

   (* Case && *)
   ASM_SIMP_TAC[] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE;
    MLK_and_intro; MLK_and_left_th; MLK_and_right_th; MLK_imp_trans]
  ;
   (* Case || *)
   EQ_TAC THENL
   [INTRO_TAC "q1q2";
    ASM_MESON_TAC[MLK_or_left_th; MLK_or_right_th; MLK_imp_trans]] THEN
   CLAIM_TAC "wq1q2" `[S . {} |~ CONJLIST w --> q1 || q2]` THENL
   [ASM_SIMP_TAC[CONJLIST_IMP_MEM]; ALL_TAC] THEN
   CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CLAIM_TAC "hq2 | hq2" `MEM q2 w \/ MEM (Not q2) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_REWRITE_TAC[];
    REFUTE_THEN (K ALL_TAC)] THEN
   SUBGOAL_THEN `~ ([S . {} |~ (CONJLIST w --> False)])` MP_TAC THENL
   [REWRITE_TAC[GSYM MLK_not_def] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT];
    REWRITE_TAC[]] THEN
   MATCH_MP_TAC MLK_frege THEN EXISTS_TAC `q1 || q2` THEN
   ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN MATCH_MP_TAC MLK_imp_swap THEN
   REWRITE_TAC[MLK_disj_imp] THEN CONJ_TAC THEN MATCH_MP_TAC MLK_imp_swap THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_axiom_not; MLK_iff_imp1; MLK_imp_trans]
 ;
 (* Case --> *)
 ASM_SIMP_TAC[] THEN EQ_TAC THENL
 [ASM_MESON_TAC[MLK_frege; CONJLIST_IMP_MEM]; INTRO_TAC "imp"] THEN
 CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
 [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
  ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_swap; MLK_add_assum];
  ALL_TAC] THEN
 MATCH_MP_TAC MLK_shunt THEN MATCH_MP_TAC MLK_imp_trans THEN
 EXISTS_TAC `q1 && Not q1` THEN CONJ_TAC THENL
 [ALL_TAC; MESON_TAC[MLK_nc_th; MLK_imp_trans; MLK_ex_falso_th]] THEN
 MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_and_right_th] THEN
 ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_trans; MLK_and_left_th]
;
(* Case <-> *)
ASM_SIMP_TAC[] THEN REMOVE_THEN "sub" (K ALL_TAC) THEN EQ_TAC THENL
[MESON_TAC[MLK_frege; MLK_add_assum; MLK_modusponens_th;
           MLK_axiom_iffimp1; MLK_axiom_iffimp2];
 ALL_TAC] THEN
INTRO_TAC "iff" THEN MATCH_MP_TAC MLK_imp_trans THEN
EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN CONJ_TAC THENL
[MATCH_MP_TAC MLK_and_intro; MESON_TAC[MLK_iff_def_th; MLK_iff_imp2]] THEN
CLAIM_TAC "rmk'"
  `!q. q SUBFORMULA p
       ==> (MEM (Not q) w <=> [S . {} |~ CONJLIST w --> Not q])` THENL
[ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE];
 ALL_TAC] THEN
CLAIM_TAC "hq1 | hq1"
  `[S . {} |~ (CONJLIST w --> q1)] \/ [S . {} |~ CONJLIST w --> Not q1]` THENL
[ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
 ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
 ALL_TAC] THEN
CLAIM_TAC "hq2 | hq2"
  `[S . {} |~ (CONJLIST w --> q2)] \/ [S . {} |~ (CONJLIST w --> Not q2)]` THENL
[ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
 ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
 ALL_TAC] THEN
ASM_MESON_TAC[MLK_nc_th; MLK_imp_trans; MLK_and_intro;
              MLK_ex_falso_th; MLK_imp_swap; MLK_shunt]
;
(* Case Box *)
INTRO_TAC "!a; a; sub; !w; w" THEN REWRITE_TAC[holds; IN_ELIM_THM] THEN
CLAIM_TAC "suba" `a SUBFORMULA p` THENL
[MATCH_MP_TAC SUBFORMULA_TRANS THEN
  EXISTS_TAC `Box a` THEN
  ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
  ALL_TAC] THEN
HYP_TAC "K" (REWRITE_RULE[FRAME; IN_ELIM_THM]) THEN
HYP_TAC "2" (REWRITE_RULE[FRAME; IN_ELIM_THM]) THEN
EQ_TAC THENL
[INTRO_TAC "boxa; !w'; (maxw' subw') r" THEN
 HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
 HYP_TAC "a: +" (SPEC `w':form list`) THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
 DISCH_THEN (SUBST1_TAC o GSYM) THEN
 REMOVE_THEN "1" (MP_TAC o SPECL [`a: form`;`w: form list`]) THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
 ALL_TAC] THEN
INTRO_TAC "3" THEN
REMOVE_THEN  "1" (MP_TAC o SPECL [`a:form`; `w:form list`]) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
DISCH_THEN SUBST1_TAC THEN INTRO_TAC "![w']; w'" THEN
REMOVE_THEN "3" (MP_TAC o SPEC `w':form list`) THEN
ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
HYP_TAC "a: +" (SPEC `w':form list`) THEN
ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
DISCH_THEN (SUBST1_TAC o GSYM) THEN REWRITE_TAC[]
]
);;
```


Completness of K
```
g `!p. K_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`;;
e (GEN_TAC);;
e (GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT {} p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                K_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP]);;
e (CONJ_TAC);;
  e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
  e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC LEMMA_K_COUNTER);;
e (ASM_REWRITE_TAC[]);;
let K_COMPLETENESS_THM = top_thm();;
```

Completness of GL
```
let COMPLETENESS_THEOREM = prove
 (`!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`,
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  INTRO_TAC "p" THEN REWRITE_TAC[valid; NOT_FORALL_THM] THEN
  EXISTS_TAC `({M | MAXIMAL_CONSISTENT GL_AX p M /\
                    (!q. MEM q M ==> q SUBSENTENCE p)},
               GL_STANDARD_REL p)` THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
  [MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GL_COUNTERMODEL_ALT THEN ASM_REWRITE_TAC[]);;
```

### Automated theorem proving and countermodel construction
