(*Sintaxa cod*)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.


Inductive ERRnat  :=
| err_nat :       ERRnat
| unsg_num :      nat  -> ERRnat.

Inductive ERRbool :=
| err_bool :      ERRbool
| boolean :       bool  -> ERRbool.

Coercion unsg_num: nat >-> ERRnat.
Coercion boolean: bool >-> ERRbool.

Inductive AExp :=
| avar: string -> AExp
| aplus: AExp  -> AExp -> AExp
| amin:  AExp  -> AExp -> AExp
| amul:  AExp  -> AExp -> AExp
| adiv:  AExp  -> AExp -> AExp
| amod:  AExp  -> AExp -> AExp.
Notation "A +' B" := (aplus A B)(at level 71, left associativity).
Notation "A -' B" := (amin  A B)(at level 71, left associativity).
Notation "A *' B" := (amul  A B)(at level 69, left associativity).
Notation "A /' B" := (adiv  A B)(at level 69, left associativity).
Notation "A %' B" := (amod  A B)(at level 68, left associativity).
Inductive BExp :=
| btrue:  BExp
| bfalse: BExp
| bnot:   BExp   -> BExp
| bvar:   string -> BExp
| blt:    AExp   -> AExp -> BExp
| ble:    AExp   -> AExp -> BExp
| bgt:    AExp   -> AExp -> BExp
| bge:    AExp   -> AExp -> BExp
| beq:    AExp   -> AExp -> BExp
| band:   BExp   -> BExp -> BExp
| bor:    BExp   -> BExp -> BExp.
Notation "A  <'  B" := (blt  A B) (at level 80).
Notation "A  <=' B" := (ble  A B) (at level 80).
Notation "A  >'  B" := (bgt  A B) (at level 80).
Notation "A  >=' B" := (bge  A B) (at level 80).
Notation "!'    A"  := (bnot   A) (at level 77, left associativity).
Notation "A &&' B"  := (band A B) (at level 78, left associativity).
Notation "A ||' B"  := (bor  A B) (at level 79, left associativity).
Inductive Stmt :=
| declNat:    string -> AExp -> Stmt
| declBool:   string -> BExp -> Stmt
| assignNat:  string -> AExp -> Stmt
| assignBool: string -> BExp -> Stmt
| sequence:   Stmt   -> Stmt -> Stmt
| while:      BExp   -> Stmt -> Stmt
| fordo:      Stmt   -> BExp -> Stmt -> Stmt -> Stmt
| ifthen:     BExp   -> Stmt -> Stmt
| ifelse:     BExp   -> Stmt -> Stmt -> Stmt.
Notation "X nat:=  A"        := (assignNat X A)(at level 100).
Notation "X bool:= A"        := (assignBool X A)(at level 100).
Notation "'NATURAL' X ::= A" := (declNat X A)(at level 100).
Notation "'BOOLEAN' X ::= A" := (declBool X A)(at level 100).
Notation "S1 ;; S2"          := (sequence S1 S2) (at level 100, right associativity).
Notation "'for' ( S1  B  S2 ) { S }" := (fordo S1 B S2 S) (at level 100).




Inductive DataType :=
| unsigned:  DataType
| boolean:  DataType.

Inductive Program :=
| p_assignment: Program
| p_function:   Program
| p_sequence:   Program -> Program -> Program.

Inductive Config :=
| 

(*
Configuratie 
    <
     cod       
     env       
     memorie   
     stack     
    >
*)


Definition Stack := list Env.





