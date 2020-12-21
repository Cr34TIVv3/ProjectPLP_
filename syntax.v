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
Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

Inductive ERRint  :=
| err_int :       ERRint
| int :       Z    -> ERRint.

Inductive ERRbool :=
| err_bool :      ERRbool
| boolean :       bool  -> ERRbool.

Inductive ERRstring :=
| err_string :    ERRstring
| str  :          string -> ERRstring.

(* array-ul va fi un fel de lista inlantuita fara operator de indexare *)

Inductive ERRarray :=
| err_array    : ERRarray
| int_array    : string -> nat -> (list Z)      -> ERRarray
| bool_array   : string -> nat -> (list bool)   -> ERRarray
| string_array : string -> nat -> (list string) -> ERRarray.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ a ]" := (cons a nil) : list_scope. 
Notation "[ a , b , .. , z ]" := (cons a (cons b .. (cons z nil) ..)) : list_scope. 

Notation "A '[-' N '-]' 'i:=' S ":=(int_array    A N S) (at level 50).
Notation "A '[-' N '-]' 'b:=' S ":=(bool_array   A N S) (at level 50).
Notation "A '[-' N '-]' 's:=' S ":=(string_array A N S) (at level 50).

Definition initializer_list := [ 1 , 2, 3].

Definition myarr := "arr" [-10-] i:= initializer_list.

Coercion int:      Z >-> ERRint.
Coercion boolean:  bool >-> ERRbool.
Coercion str:      string >-> ERRstring.


Inductive AExp :=
| avar: string -> AExp
| anum: ERRint -> AExp
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
Coercion anum: ERRint >-> AExp.
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
Notation "A  'b<'  B" := (blt  A B) (at level 80).
Notation "A  'b<=' B" := (ble  A B) (at level 80).
Notation "A  'b>'  B" := (bgt  A B) (at level 80).
Notation "A  'b>=' B" := (bge  A B) (at level 80).
Notation "b!       A" := (bnot   A) (at level 77, left associativity).
Notation "A  'b='  B" := (beq  A B) (at level 80).
Notation "A  'b&&' B" := (band A B) (at level 78, left associativity).
Notation "A  'b||' B" := (bor  A B) (at level 79, left associativity).
Coercion bconst: ERRbool >-> BExp.
Coercion bvar: string >-> BExp.

Check true b&& true.
Check "aa" b< "bb".
Check true b|| false.
Check true b|| "var".

Inductive StrExp :=
| strconst : ERRstring -> StrExp
| strvar :   string    -> StrExp
| strcat :   StrExp    -> StrExp -> StrExp
| strtimes : StrExp    -> nat    -> StrExp.
Notation "A  's+'  B" := (strcat A B)   (at level 82).
Notation "A  's*'  n" := (strtimes A n) (at level 81).
Coercion strconst: ERRstring >-> StrExp.
(* Coercion strvar:   string    >-> StrExp. *)

Check "Mos" s+ "Craciun".


Inductive ArrExp :=
| arr_length :          ERRarray -> ArrExp
| arr_add_nat_item :    ERRarray -> nat        ->  ArrExp
| arr_add_int_item :    ERRarray -> Z          ->  ArrExp
| arr_add_bool_item :   ERRarray -> bool       ->  ArrExp
| arr_add_str_item :    ERRarray -> string     ->  ArrExp
| arr_del_nat_item:     ERRarray -> nat        ->  ArrExp
| arr_del_int_item:     ERRarray -> Z          ->  ArrExp
| arr_del_bool_item:    ERRarray -> bool       ->  ArrExp
| arr_del_str_item:     ERRarray -> string     ->  ArrExp
| arr_getitem:          ERRarray -> nat        ->  ArrExp.
Notation "'@' A"        :=(arr_length          A) (at level 67).
Notation "A 'n<-'  I"   :=(arr_add_nat_item  A I) (at level 68).
Notation "A 'i<-'  I"   :=(arr_add_int_item  A I) (at level 68).
Notation "A 'b<-'  I"   :=(arr_add_bool_item A I) (at level 68).
Notation "A 's<-'  I"   :=(arr_add_str_item  A I) (at level 68).
Notation "A 'n<-X' I"   :=(arr_del_nat_item  A I) (at level 66).
Notation "A 'i<-X' I"   :=(arr_del_int_item  A I) (at level 66).
Notation "A 'b<-X' I"   :=(arr_del_bool_item A I) (at level 66).
Notation "A 's<-X' I"   :=(arr_del_str_item  A I) (at level 66).
Notation "A '[[' N ']]'":=(arr_getitem       A N) (at level 69).


Check @ myarr.
Check myarr[[ 3 ]].

Inductive Stmt :=
| declInt_l:      string -> AExp   -> Stmt
| declBool_l:     string -> BExp   -> Stmt
| declStr_l:      string -> StrExp -> Stmt

| declIntArr_l:   string -> nat    -> Stmt
| declBoolArr_l:  string -> nat    -> Stmt
| declStrArr_l:   string -> nat    -> Stmt

| assignInt_l:    string -> AExp   -> Stmt
| assignBool_l:   string -> BExp   -> Stmt
| assignStr_l:    string -> StrExp -> Stmt

| assiIntArr_l:   ERRarray         -> Stmt
| assiBoolArr_l:  ERRarray         -> Stmt
| assiStrArr_l:   ERRarray         -> Stmt


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
| callLambda: string -> Stmt   -> Stmt -> Stmt
| returnFun:  list string      -> Stmt.

Notation "'INTEGER' X := I"                := (declInt_l X I)       (at level 90).
Notation "'BOOLEAN' X := B"                := (declBool_l X B)      (at level 90).
Notation "'STRING'  X := S"                := (declStr_l X S)       (at level 90).
Notation "X int:=  I"                      := (assignInt_l X I)     (at level 90).
Notation "X bool:= B"                      := (assignBool_l X B)    (at level 90).
Notation "X str:=  S"                      := (assignStr_l X S)     (at level 90).
Notation "'INTEGER' X '[-' N '-]' := L"    := (assiIntArr_l X N L)  (at level 90).
Notation "'BOOL'    X '[-' N '-]' := L"    := (assiBoolArr_l X N L) (at level 90).
Notation "'STRING'  X '[-' N '-]' := L"    := (assiStrArr_l X N L)  (at level 90).
Notation "S1 ;; S2"                        := (sequence S1 S2)      (at level 93, right associativity).
Notation "'while' ( B )  { S }"            := (whiledo B S)         (at level 89).
Notation "'for' ( S1  B  S2 ) { S }"       := (fordo S1 B S2 S)     (at level 91).
Notation "'if' ( B ) { S1 } 'else' { S2 }" := (ifelse B S1 S2)      (at level 91).
Notation "'IF' ( B ) { S }"                := (ifthen B S)          (at level 91).
Notation "'switch' ( A ) { S }"            := (switch A S)          (at level 90).
Notation "'case' :: A    S"                := (case A S)            (at level 90).
Notation "'call' N ( S1 )"                 := (callFun N S1)        (at level 90).
Notation "'<return>' S"                    := (returnFun S)         (at level 90).
Check INTEGER "asd" := 2.

Inductive Program :=
| seqPrg:        Program -> Program -> Program
| declMain:      Stmt    -> Program
| declFun:       string  -> list string  -> Stmt     -> Program

| declInt_g:     string  -> AExp   -> Program
| declBool_g:    string  -> BExp   -> Program
| declStr_g:     string  -> StrExp -> Program

| declClass:     string  -> Stmt   -> Program.
Notation "P1 '|' P2"                   := (seqPrg P1 P2)   (at level 100).
Notation "'MAIN' '{(' S ')}'"          := (declMain S)     (at level 90).
Notation "'function' N  S  '{' S1 '}'" := (declFun N S S1) (at level 90).
Notation "'GLOBAL' 'INTEGER' X ':=' I" := (declInt_g X I)  (at level 90).
Notation "'GLOBAL' 'BOOL'    X ':=' I" := (declInt_g X I)  (at level 90).
Notation "'GLOBAL' 'STRING'  X ':=' I" := (declInt_g X I)  (at level 90).


Check INTEGER "LVAL" := 2.

Check function "cmmdc" [ "x" , "y" ] 
{  
    INTEGER "LVAL" := 2 
}. 


Definition mycode :=
GLOBAL INTEGER "g_var" := 3 |

function "cmmdc" [ "x" , "y" ]  
{(
      while (!b "x" b= "y" )
      {(
           if ( "x" b> "y" )
           {(
              "x" = "x" - "y" 
           })
           else
           {(
              "y" = "y" - "x" 
           )}
      )} ;;
      
      <return> [ "x" ]
)}

MAIN
{(
      INTEGER "X" := 3 ;;
      INTEGER "Y" := 9 ;;
      call "cmmdc" [ "X" , "Y" ]
)}.



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




