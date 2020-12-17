(*
switch

lambda

tipuri de variabile


functii + functii de conversie intre tipuri de date


clase


tablouri
*)

(*Sintaxa cod*)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(*ERRnat si ERRbool sunt pentru situatiile in care pot aparea erori *)

Inductive ERRnat  :=
| err_nat :       ERRnat
| unsg_num :      nat  -> ERRnat.

Inductive ERRbool :=
| err_bool :      ERRbool
| boolean :       bool  -> ERRbool.

Inductive ERRstring :=
| err_string :    ERRstring
| str  :          string -> ERRstring.

Coercion unsg_num: nat >-> ERRnat.
Coercion boolean: bool >-> ERRbool.
Coercion str:   string >-> ERRstring.

Inductive AExp :=
| avar: string -> AExp
| anum: ERRnat -> AExp
| aplus: AExp  -> AExp -> AExp
| amin:  AExp  -> AExp -> AExp
| amul:  AExp  -> AExp -> AExp
| adiv:  AExp  -> AExp -> AExp
| amod:  AExp  -> AExp -> AExp.
Notation "A a+ B" := (aplus A B)(at level 71, left associativity).
Notation "A a- B" := (amin  A B)(at level 71, left associativity).
Notation "A a* B" := (amul  A B)(at level 69, left associativity).
Notation "A a/ B" := (adiv  A B)(at level 69, left associativity).
Notation "A a% B" := (amod  A B)(at level 68, left associativity).
Coercion anum: ERRnat >-> AExp.
Coercion avar: string >-> AExp. 
Inductive BExp :=
| bconst: ERRbool-> BExp
| bvar:   string -> BExp
| bnot:   BExp   -> BExp
| blt:    AExp   -> AExp -> BExp
| ble:    AExp   -> AExp -> BExp
| bgt:    AExp   -> AExp -> BExp
| bge:    AExp   -> AExp -> BExp
| beq:    AExp   -> AExp -> BExp
| band:   BExp   -> BExp -> BExp
| bor:    BExp   -> BExp -> BExp.
Notation "A  b<  B" := (blt  A B) (at level 80).
Notation "A  b<= B" := (ble  A B) (at level 80).
Notation "A  b>  B" := (bgt  A B) (at level 80).
Notation "A  b>= B" := (bge  A B) (at level 80).
Notation "b!     A" := (bnot   A) (at level 77, left associativity).
Notation "A  b&& B"  := (band A B) (at level 78, left associativity).
Notation "A  b|| B"  := (bor  A B) (at level 79, left associativity).
Coercion bconst: ERRbool >-> BExp.
Inductive StrExp :=
| strconst : ERRstring -> StrExp
| strcat :   StrExp    -> StrExp -> StrExp
| strtimes : StrExp    -> nat    -> StrExp.
Notation "A  s+  B" := (strcat A B) (at level 82).
Notation "A  s*  n" := (strtimes A n) (at level 81).
Coercion strconst: ERRstring >-> StrExp.
Inductive Stmt :=
| declNat:    string -> AExp   -> Stmt
| declBool:   string -> BExp   -> Stmt
| declStr:    string -> StrExp -> Stmt

| assignNat:  string -> AExp   -> Stmt
| assignBool: string -> BExp   -> Stmt
| assignStr:  string -> StrExp -> Stmt

| sequence:   Stmt   -> Stmt   -> Stmt
| whiledo:    BExp   -> Stmt   -> Stmt
| fordo:      Stmt   -> BExp   -> Stmt -> Stmt -> Stmt
| ifthen:     BExp   -> Stmt   -> Stmt
| ifelse:     BExp   -> Stmt   -> Stmt -> Stmt

| break:      Stmt
| continue:   Stmt

| 
Notation "X nat:=  A"                      := (assignNat X A)   (at level 100).
Notation "X bool:= A"                      := (assignBool X A)  (at level 100).
Notation "'NATURAL' X ::= A"               := (declNat X A)     (at level 100).
Notation "'BOOLEAN' X ::= A"               := (declBool X A)    (at level 100).
Notation "S1 ;; S2"                        := (sequence S1 S2)  (at level 100, right associativity).
Notation "'while' ( B ) { S }"             := (whiledo B S)     (at level 100).
Notation "'for' ( S1  B  S2 ) { S }"       := (fordo S1 B S2 S) (at level 100).
Notation "'if' ( B ) { S }"                := (ifthen B S)      (at level 100).
Notation "'if' ( B ) { S1 } 'else' { S2 }" := (ifelse B S1 S2)  (at level 100).

Inductive Result :=
| subCode :         Stmt      -> Result (*functiile trebuie mapate cu codul lor*)
| errUndecl :       Result
| errAssign :       Result
| natResult :       ERRnat  -> Result
| booleanResult :   ERRbool -> Result
| default :         Result. 


(* This function is useful when we need to update the environment based on the state of a variable *)
Definition equalOverTypes (type1 : Result) (type2 : Result) : bool :=
  match type1 with
| subCode sc1       => match type2 with 
                    | subCode sc2 => true
                    | _ => false
                      end
| errAssign         => match type2 with 
                    | errAssign => true
                    | _ => false
                      end
| errUndecl         => match type2 with 
                    | errUndecl => true
                    | _ => false
                      end
| default           => match type2 with 
                    | default => true
                    | _ => false
                      end
| natResult  x      => match type2 with 
                    | natResult y => true
                    | _ => false
                      end
| booleanResult x   =>match type2 with 
                    | booleanResult y => true
                    | _ => false
                      end
  end.


Inductive typeOfMemory :=
  | tOM_default : typeOfMemory
  | offset :  nat -> typeOfMemory. (* contor pentru zona de memorie *)


Scheme Equality for Mem.


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





