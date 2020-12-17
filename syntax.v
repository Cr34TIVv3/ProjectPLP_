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

(* Inductive Array_value :=
(* | error_array : Array_value *)
| empty_array : Array_value
(* | start_array : Z->Array_value *)
| Carray : Array_value -> nat -> Array_value.

Definition myarray := empty_array.
Definition mynewarray := Carray myarray 5.


Compute empty_array.
Compute Carray mynewarray 25. *)


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
Notation "A  b=  B" := (beq  A B) (at level 80).
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
| declNat_l:  string -> AExp   -> Stmt
| declBool_l: string -> BExp   -> Stmt
| declStr_l:  string -> StrExp -> Stmt

| assignNat:  string -> AExp   -> Stmt
| assignBool: string -> BExp   -> Stmt
| assignStr:  string -> StrExp -> Stmt

| sequence:   Stmt   -> Stmt   -> Stmt
| whiledo:    BExp   -> Stmt   -> Stmt
| fordo:      Stmt   -> BExp   -> Stmt -> Stmt -> Stmt

| ifelse:     BExp   -> Stmt   -> Stmt -> Stmt
| ifthen:     BExp   -> Stmt   -> Stmt

| switch:     AExp   -> Stmt   -> Stmt
| case:       AExp   -> Stmt   -> Stmt

| break:      Stmt
| continue:   Stmt

| callFun:    string -> Stmt   -> Stmt
| callLambda: string -> Stmt   -> Stmt -> Stmt.

Notation "'NATURAL' X := N"                := (declNat X N)     (at level 100).
Notation "'BOOLEAN' X := B"                := (declBool X B)    (at level 100).
Notation "'STRING'  X := S"                := (declStr X S)     (at level 100).
Notation "X nat:=  N"                      := (assignNat X N)   (at level 100).
Notation "X bool:= B"                      := (assignBool X B)  (at level 100).
Notation "X str:=  S"                      := (assignStr X S)   (at level 100).
Notation "S1 ;; S2"                        := (sequence S1 S2)  (at level 100, right associativity).
Notation "'while' ( B )  { S }"            := (whiledo B S)     (at level 100).
Notation "'for' ( S1  B  S2 ) { S }"       := (fordo S1 B S2 S) (at level 100).
Notation "'if' ( B ) { S1 } 'else' { S2 }" := (ifelse B S1 S2)  (at level 100).
Notation "'IF' ( B ) { S }"                := (ifthen B S)      (at level 100).
Notation "'switch' ( A ) { S }"            := (switch A S)      (at level 100).
Notation "'case' :: A    S"                := (case A S)        (at level 100).
Notation "'call' N ( S1 )"                 := (callFun N S1)    (at level 100).

Inductive Program :=
| seqPrg:       Program -> Program -> Program
| declMain:     Stmt    -> Program
| declFun:      string  -> Stmt    -> Stmt     -> Program

| declNat_g:    string  -> AExp   -> Program
| declBool_g:   string  -> BExp   -> Program
| declStr_g:    string  -> StrExp -> Program

| declClass:    string  -> Stmt   -> Program.
Notation "P1 P2"  := (seqPrg P1 P2) (at level 100).
Notation "'MAIN' '()' { S }" := (declMain S) (at level 100).
Notation "'function' N ( S ) { SS }" := (declFun N S SS) (at level 100).
Notation "'GLOBAL' 'NATURAL' x"








Inductive Result :=
| subCode :         Stmt    -> Result (*functiile trebuie mapate cu codul lor*)
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




