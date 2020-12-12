(*Sintaxa cod*)
Require Import String.


Scheme Equality for string.

Inductive AExp :=
| avar: string -> AExp
| aplus: AExp  -> AExp -> AExp
| amin:  AExp  -> AExp -> AExp
| amul:  AExp  -> AExp -> AExp
| adiv:  AExp  -> AExp -> AExp
| amod:  AExp  -> AExp -> AExp.

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

Inductive Stmt :=
| declNat:  string -> AExp -> Stmt
| declBool: string -> BExp -> Stmt
| sequence: Stmt   -> Stmt -> Stmt
| while:    BExp   -> Stmt -> Stmt
| fordo:    Stmt   -> BExp -> Stmt -> Stmt -> Stmt
| ifthen:   BExp   -> Stmt -> Stmt
| ifelse:   BExp   -> Stmt -> Stmt -> Stmt.



