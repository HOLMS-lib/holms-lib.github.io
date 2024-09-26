# HOLMS - A HOL-Light Library for Modal Systems

To be done.

Example of code:
```
let MODPROVES_RULES,MODPROVES_INDUCT,MODPROVES_CASES =
  new_inductive_definition
  `(!H p. KAXIOM p ==> [S . H |~ p]) /\
   (!H p. p IN S ==> [S . H |~ p]) /\
   (!H p. p IN H ==> [S . H |~ p]) /\
   (!H p q. [S . H |~ p --> q] /\ [S . H |~ p] ==> [S . H |~ q]) /\
   (!H p. [S . {} |~ p] ==> [S . H |~ Box p])`;;
```
