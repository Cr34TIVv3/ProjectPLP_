Require Import Strings.String.
Scheme Equality for string.


          (*  types definitions + operations *)
  
  (* natural *)


Require Import Nat.

Inductive ERRnat  :=
| err_nat :       ERRnat
| natural :       nat    -> ERRnat.

Coercion natural:  nat >-> ERRnat.

Inductive AExp :=
| acon: ERRnat -> AExp
| avar: string -> AExp
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

Coercion acon: ERRnat >-> AExp.
Coercion avar: string >-> AExp. 


  (* booleans *)

Inductive ERRbool :=
| err_bool :      ERRbool
| boolean :       bool  -> ERRbool.

Coercion boolean:  bool >-> ERRbool.

Inductive BExp :=
| bcon:   ERRbool-> BExp
| bvar:   string -> BExp
| bnot:   BExp   -> BExp
| blt:    AExp   -> AExp -> BExp
| ble:    AExp   -> AExp -> BExp
| beq:    AExp   -> AExp -> BExp
| band:   BExp   -> BExp -> BExp
| bor:    BExp   -> BExp -> BExp.
Notation "b!       A" := (bnot   A) (at level 77, left associativity).
Notation "A  b<  B" := (blt  A B) (at level 80).
Notation "A  b<= B" := (ble  A B) (at level 80).
Notation "A  b=  B" := (beq  A B) (at level 80).
Notation "A  b&& B" := (band A B) (at level 78, left associativity).
Notation "A  b|| B" := (bor  A B) (at level 79, left associativity).

Coercion bcon : ERRbool >->  BExp.
Coercion bvar : string >-> BExp.


  (* strings *)

Inductive ERRstring :=
| err_str :       ERRstring
| str  :          string -> ERRstring.

Coercion str: string >-> ERRstring.

Inductive SExp :=
| scon : ERRstring -> SExp
| svar :   string    -> SExp
| scat :   SExp    -> SExp -> SExp.
Notation "A s+ B" := (scat A B) (at level 71).

Coercion svar : string >-> SExp.


(* statements *)
Inductive Stmt :=
| declNat:        string -> AExp   -> Stmt
| declBool:       string -> BExp   -> Stmt
| declStr:        string -> SExp -> Stmt

| assignNat:      string -> AExp   -> Stmt
| assignBool:     string -> BExp   -> Stmt
| assignStr:      string -> SExp -> Stmt

| funDecl:        string -> Stmt   -> Stmt -> Stmt
| funCall:        string -> Stmt

| sequence:   Stmt   -> Stmt   -> Stmt

| whiledo:    BExp   -> Stmt   -> Stmt

| ifelse:     BExp   -> Stmt   -> Stmt -> Stmt
| ifthen:     BExp   -> Stmt   -> Stmt

| switch_:     AExp   -> Stmt   -> Stmt
| case_:       AExp   -> Stmt   -> Stmt

| break:      Stmt
| void:        Stmt.
Notation "'NATURAL' X :n= N"                := (declNat  X N)      (at level 90).
Notation "'BOOLEAN' X :b= B"                := (declBool X B)      (at level 90).
Notation "'STRING'  X :s= S"                := (declStr  X S)      (at level 90).
Notation "X <n-  N"                         := (assignNat X N)     (at level 90).
Notation "X <b-  N"                         := (assignBool X N)    (at level 90).
Notation "X <s-  N"                         := (assignStr X N)     (at level 90).
Notation "'function' N # P # '{' S '}'"     := (funDecl N P S)     (at level 91).
Notation "'CALL' N "                        := (funCall N)         (at level 90).
Notation "S1 ;; S2"                         := (sequence S1 S2)    (at level 92, right associativity).
Notation "'while' '[' B ']'  S "            := (whiledo B S)       (at level 89).
(*ifelse*)
(*ifthen*)
(* Notation "'switch' A  '[' S ']'"            := (switch A S)        (at level 90). *)
(* Notation "'case' '>' A '<' S "              := (case A S)          (at level 90). *)


Inductive Result :=
| code :            Stmt      -> Result 
| undeclared :      Result
| naturalResult :   ERRnat    -> Result
| booleanResult :   ERRbool   -> Result
| stringResult :    ERRstring -> Result.


Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
| code c => match t2 with 
                   | code c => true
                   | _ => false
                   end
| undeclared => match t2 with 
                   | undeclared => true
                   | _ => false
                   end
| naturalResult n=> match t2 with 
                   | naturalResult n=> true
                   | _ => false
                   end
| booleanResult n=> match t2 with 
                   | booleanResult n=> true
                   | _ => false
                   end
| stringResult n=> match t2 with 
                   | stringResult n=> true
                   | _ => false
                   end
  end.


(*result for natural*)

Definition aplus_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural x' )) , (naturalResult ( natural y' )) => (naturalResult ( natural ( x' + y' ) )) 
    | _ , _                                                           =>  naturalResult err_nat
  end.

Definition amin_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural x' )) , (naturalResult ( natural y' )) => if(Nat.ltb x' y') then (naturalResult err_nat)
                                                                                           else (naturalResult (natural ( x' - y' )))
    | _ , _                                                           =>  naturalResult err_nat
  end.

Definition amul_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural x' )) , (naturalResult ( natural y' )) => (naturalResult ( natural ( x' * y' ) )) 
    | _ , _                                                           =>  naturalResult err_nat
  end.

Definition adiv_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural x' )) , (naturalResult ( natural y' )) => match x', y' with
                                                                         |  x'', 0  => naturalResult (err_nat)
                                                                         |  x'', y''=> naturalResult ( natural ( x'' / y'' ) )
                                                                         end
    | _ , _                                                           =>  naturalResult err_nat
  end.

Definition amod_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural x' )) , (naturalResult ( natural y' )) => match x', y' with
                                                                         |  x'', 0  => naturalResult (err_nat)
                                                                         |  x'', y''=> naturalResult ( natural ( x'' mod y'' ) )
                                                                         end
    | _ , _                                                           =>  naturalResult err_nat
  end.





(*result for booleans*)

Definition bnot_result (x : Result) : Result :=
  match x with
    | booleanResult ( boolean true  ) => booleanResult ( boolean false )
    | booleanResult ( boolean false ) => booleanResult ( boolean true  )
    | _                               => booleanResult   err_bool
  end.

Definition blt_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural n1 )) , (naturalResult ( natural n2 )) => if ( n1 <? n2 ) then booleanResult ( boolean true )
                                                                                        else booleanResult ( boolean false)   
    | _ , _                                                           =>  booleanResult err_bool
  end.

Definition ble_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural n1 )) , (naturalResult ( natural n2 )) => if ( n1 <=? n2 ) then booleanResult ( boolean true )
                                                                                        else booleanResult ( boolean false)   
    | _ , _                                                           =>  booleanResult err_bool
  end.

Definition beq_result (x y : Result) : Result :=
  match x, y with
    | (naturalResult ( natural n1 )) , (naturalResult ( natural n2 )) => if ( n1 =? n2 ) then booleanResult ( boolean true )
                                                                                        else booleanResult ( boolean false)   
    | _ , _                                                           =>  booleanResult err_bool
  end.

Definition band_result (x y : Result) : Result :=
  match x, y with
    | (booleanResult ( boolean true  )) , (booleanResult ( boolean true  )) => booleanResult ( boolean true  )
    | (booleanResult ( boolean true  )) , (booleanResult ( boolean false )) => booleanResult ( boolean false )
    | (booleanResult ( boolean false )) , (booleanResult ( boolean true  )) => booleanResult ( boolean false )
    | (booleanResult ( boolean false )) , (booleanResult ( boolean false )) => booleanResult ( boolean false )  
    | _ , _                                                                 => booleanResult   err_bool
  end.

Definition bor_result (x y : Result) : Result :=
  match x, y with
    | (booleanResult ( boolean true  )) , (booleanResult ( boolean true  )) => booleanResult ( boolean true  )
    | (booleanResult ( boolean true  )) , (booleanResult ( boolean false )) => booleanResult ( boolean true  )
    | (booleanResult ( boolean false )) , (booleanResult ( boolean true  )) => booleanResult ( boolean true  )
    | (booleanResult ( boolean false )) , (booleanResult ( boolean false )) => booleanResult ( boolean false )  
    | _ , _                                                                 => booleanResult   err_bool
  end.


(*result for strings*)

Definition scat_result (x y : Result) : Result :=
  match x, y with
    | (stringResult ( str s1 )) , (stringResult ( str s2 )) => stringResult ( str ( s1 ++ s2   ) )
    | _ , _                                                 => stringResult ( err_str )
  end. 



(* environment + semantics*)

Definition Env := string -> Result.

Definition env0 : Env := fun x => undeclared.

Definition update (env : Env) (x : string) (v : Result) : Env :=
fun y=>
  if ( string_eq_dec y x )  then v
                            else (env y)
.




Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : AExp -> Env -> Result -> Prop :=
| a_const :   forall n sigma,    
                acon n =[ sigma ]=> (naturalResult n)
| a_var :     forall v sigma,    
                avar v =[ sigma ]=> (sigma v)
| a_add :     forall a1 a2 i1 i2 sigma n,
                a1 =[ sigma ]=> i1 ->
                a2 =[ sigma ]=> i2 ->
                n = aplus_result i1 i2 -> 
                (a1 a+ a2) =[ sigma ]=> n
| a_minus :   forall a1 a2 i1 i2 sigma n,
                a1 =[ sigma ]=> i1 ->
                a2 =[ sigma ]=> i2 ->
                n = amin_result i1 i2 -> 
                (a1 a- a2) =[ sigma ]=> n
| a_times :   forall a1 a2 i1 i2 sigma n,
                a1 =[ sigma ]=> i1 ->
                a2 =[ sigma ]=> i2 ->
                n = amul_result i1 i2 -> 
                (a1 a* a2) =[ sigma ]=> n
| a_divide :  forall a1 a2 i1 i2 sigma n,
                a1 =[ sigma ]=> i1 ->
                a2 =[ sigma ]=> i2 ->
                n = adiv_result i1 i2 -> 
                (a1 a/ a2) =[ sigma ]=> n
| a_modullo : forall a1 a2 i1 i2 sigma n,
                a1 =[ sigma ]=> i1 ->
                a2 =[ sigma ]=> i2 ->
                n = amod_result i1 i2 -> 
                (a1 a% a2) =[ sigma ]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Reserved Notation "B ={ E }=> B'" (at level 60).
Inductive beval : BExp -> Env -> Result -> Prop :=
| b_const :   forall b env,    
                bcon b ={ env }=> booleanResult b
| b_var :     forall v env,    
                bvar v ={ env }=> (env v)
| b_not :     forall b i env n,
                b ={ env }=> i ->
                n = bnot_result i -> 
                (b! b) ={ env }=> n
| b_ltb :   forall a1 a2 i1 i2 env n,
                a1 =[ env ]=> i1 ->
                a2 =[ env ]=> i2 ->
                n = blt_result i1 i2 -> 
                (a1 b< a2) ={ env }=> n
| b_lte :   forall a1 a2 i1 i2 env n,
                a1 =[ env ]=> i1 ->
                a2 =[ env ]=> i2 ->
                n = ble_result i1 i2 -> 
                (a1 b<= a2) ={ env }=> n
| b_eqb :  forall a1 a2 i1 i2 env n,
                a1 =[ env ]=> i1 ->
                a2 =[ env ]=> i2 ->
                n = beq_result i1 i2 -> 
                (a1 b= a2) ={ env }=> n
| b_and : forall b1 b2 i1 i2 env n,
                b1 ={ env }=> i1 ->
                b2 ={ env }=> i2 ->
                n = band_result i1 i2 -> 
                (b1 b&& b2) ={ env }=> n
| b_or : forall b1 b2 i1 i2 env n,
                b1 ={ env }=> i1 ->
                b2 ={ env }=> i2 ->
                n = bor_result i1 i2 -> 
                (b1 b|| b2) ={ env }=> n
where "B ={ env }=> B'" := (beval B env B').

Reserved Notation "S =# V #=> S'" (at level 60).
Inductive seval : SExp -> Env -> Result -> Prop :=
| s_const :   forall s env,    
                scon s =# env #=> stringResult s
| s_var :     forall v env,    
                svar v =# env #=> (env v)
| s_cat :     forall s1 s2 i1 i2 env n,
                s1 =# env #=> i1 ->
                s2 =# env #=> i2 ->
                n = scat_result i1 i2 -> 
                (s1 s+ s2) =# env #=> n
where "M =# S #=> N'" := (seval M S N').


Scheme Equality for Result.


Reserved Notation "S1 -! E !-> S2" (at level 70).
Inductive eval : Stmt -> Env -> Env -> Prop := 
| e_declNat :   forall x i n sigma sigma',
                  ( Result_beq undeclared (sigma x) ) = true ->
                  n =[ sigma ]=> (naturalResult i)             ->
                  sigma' = (update sigma x (naturalResult i))  ->
                  ( NATURAL x :n= n ) -! sigma !-> sigma'
| e_declBool :  forall x i n sigma sigma',
                  ( Result_beq undeclared (sigma x) ) = true ->
                  n ={ sigma }=> (booleanResult i)             ->
                  sigma' = (update sigma x (booleanResult i))  ->
                  ( BOOLEAN x :b= n ) -! sigma !-> sigma'
| e_declStr :   forall x i n sigma sigma',
                  ( Result_beq undeclared (sigma x) ) = true ->
                  n =# sigma #=> (stringResult i)              ->
                  sigma' = (update sigma x (stringResult i))  ->
                  ( STRING x :s= n ) -! sigma !-> sigma'

| e_assignNat : forall x i a sigma sigma',
                  ( Result_beq undeclared (sigma x) ) = false->
                  a =[ sigma ]=> (naturalResult i)             ->
                  sigma' = (update sigma x (naturalResult i))  ->
                  ( x <n- a ) -! sigma !-> sigma'      
| e_assignBool :forall x i a sigma sigma',
                  ( Result_beq undeclared (sigma x) ) = false->
                  a =[ sigma ]=> (booleanResult i)             ->
                  sigma' = (update sigma x (booleanResult i))  ->
                  ( x <n- a ) -! sigma !-> sigma'
| e_assignStr : forall x i a sigma sigma',
                  ( Result_beq undeclared (sigma x) ) = false->
                  a =[ sigma ]=> (stringResult i)             ->
                  sigma' = (update sigma x (stringResult i))   ->
                  ( x <n- a ) -! sigma !-> sigma'

| e_funDecl :   forall s P stmt sigma sigma',
                  P = void ->
                  (Result_beq undeclared (sigma s)) = true     ->
                  sigma' = (update sigma s (code stmt))        -> 
                  funDecl s P stmt -! sigma !-> sigma' 
| e_funCall :   forall save s sigma sigma',
                  (Result_beq undeclared (sigma save)) = false ->
                  sigma save = (code s)                        -> 
                  s -! sigma !-> sigma'                        ->
                  funCall save -! sigma !-> sigma'

| e_sequence :  forall s1 s2 sigma sigma1 sigma2,
                  s1 -! sigma  !-> sigma1                      ->
                  s2 -! sigma1 !-> sigma2                      ->
                  (s1 ;; s2) -! sigma !-> sigma2


| e_whilefalse: forall b s sigma,
                  b ={ sigma }=> booleanResult false           ->
                  (whiledo b s)-! sigma !-> sigma  
| e_whiletrue:  forall b s sigma sigma',
                  b ={ sigma }=> booleanResult true            ->
                  ( s ;; whiledo b s)-! sigma !-> sigma'       ->
                  (whiledo b s)-! sigma !-> sigma'
| e_whilebreak: forall b s s1 s2 sigma sigma',
                  b  ={ sigma }=> booleanResult true           ->
                  s  = (s1 ;; break ;; s2)                     ->
                  s1 -! sigma !-> sigma'                       ->
                  whiledo b s -! sigma !-> sigma'

|e_switch_seq_false : forall a i a1 i1 sigma sigma' s s1 s2,
                  a =[ sigma ]=> i                             ->
                  s = ((case_ (a1) (s1)) ;; s2)                 ->
                  a1 =[ sigma ]=> i1                           ->
                  false = Result_beq i i1                      ->
                  (switch_ a s2)  -! sigma !-> sigma'           ->
                  (switch_ a s )  -! sigma !-> sigma'
| e_switch_seq_true : forall a i a1 i1 sigma sigma' sigma'' s s1 s2,
                  a =[ sigma ]=> i                             ->
                  s = ((case_ a1 s1) ;; s2)                     ->
                  a1 =[ sigma ]=> i1                           ->
                  i = i1                                       -> 
                  s1 -! sigma !-> sigma'                       ->
                  switch_ a s2 -! sigma' !-> sigma''            ->
                  switch_ a s  -! sigma  !-> sigma''
| e_switch_case_true : forall a i a1 i1 sigma sigma' s s1,
                  a =[ sigma ]=> i                             ->
                  s = (case_ a1 s1)                             ->
                  a1 =[ sigma ]=> i1                           ->
                  i = i1                                       ->
                  s1 -! sigma !-> sigma'                       ->
                  switch_ a s -! sigma !-> sigma'
| e_switch_case_false : forall a i a1 i1 sigma s s1,
                  a =[ sigma ]=> i ->
                  s = (case_ a1 s1) ->
                  a1 =[ sigma ]=> i1 ->
                  false = Result_beq i i1 ->
                  switch_ a s -! sigma !-> sigma 
where "M' -! S' !-> N'" := (eval M' S' N'). 



Definition function_ex  :=
function "fun" # void # 
{
  NATURAL "var" :n= 5
} ;;
CALL "fun";;
NATURAL "x" :n= 1.

Example ex1 : exists ENV, function_ex -! env0 !-> ENV.
Proof.
    eexists.
    unfold function_ex.
    eapply e_sequence.
        -eapply e_funDecl.
            + reflexivity.
            + simpl. reflexivity.
            + split.
        -eapply e_sequence.
            +eapply e_funCall.
                -- simpl. reflexivity.
                -- split. 
                -- eapply e_declNat.
                        ++ simpl. reflexivity.
                        ++ eapply a_const.
                        ++ split.
            + eapply e_declNat.
                -- simpl. reflexivity.
                -- eapply a_const. 
                -- split.
Qed.
        


Definition switch_ex :=
NATURAL "x" :n= 5 ;;
switch_ ( 5 )
(
  case_ 5   ( "x" <n- 0 ) ;;
  case_ 6   ( "x" <n- 1 )
). 


Example ex2 : exists ENV, switch_ex -! env0 !-> ENV.
Proof.
    eexists.
    unfold switch_ex.
    eapply e_sequence.
          -eapply e_declNat.
                + simpl. reflexivity.
                + eapply a_const.
                + split.
          -eapply e_switch_seq_true.
                +eapply a_const.
                +intuition.
                +eapply a_const.
                +reflexivity.
                +eapply e_assignNat.
                    --simpl. reflexivity.
                    --eapply a_const.
                    --split.
                +eapply e_switch_case_false.
                    --eapply a_const.
                    --intuition.
                    --eapply a_const.
                    --simpl. reflexivity.
Qed.


Definition break_ex :=
whiledo (1 b< 10)
(
  NATURAL "a" :n= 3 ;;
  NATURAL "x" :n= 5 ;;
  break
). 

Inductive BExp1 :=
| b_True:  BExp1
| b_False: BExp1
| b_Var:   string -> BExp1
| b_Not:   BExp1  -> BExp1
| b_And:   BExp1  -> BExp1 -> BExp1
| b_Or:    BExp1  -> BExp1 -> BExp1.

Notation " a &&' b" := (b_And a b ) (at level 50).
Notation " a ||' b" := (b_Or a b ) (at level 50).
Notation " !!' b" := (b_Not b ) (at level 50).

Definition EnvB := string ->bool.
Definition envB := fun x => if string_dec x "var" then false else true.

Require Import Bool.


Fixpoint interpret (e : BExp1) (env : EnvB) : bool :=
  match e with
  | b_True      => true
  | b_False     => false
  | b_Var x     => (env x)
  | b_Not b     => negb (interpret b env)
  | b_And b1 b2 => andb (interpret b1 env) (interpret b2 env)
  | b_Or  b1 b2 => orb  (interpret b1 env) (interpret b2 env)
  end.


(* Define a stack machine *)
Inductive Instruction :=
| push_const :  bool   -> Instruction
| push_var :    string -> Instruction
| not_exp :     Instruction
| and_exp :     Instruction
| or_exp :      Instruction.

Require Import List.
Import ListNotations.

Definition Stack := list bool.
Definition run_instruction (i : Instruction)
         (env : EnvB) (stack : Stack) : Stack :=
  match i with
  | push_const c => (c :: stack)
  | push_var x   => ((env x) :: stack)
  | not_exp      => match stack with
                 | n1 :: stack' => ( negb n1) :: stack'
                 | _ => stack
                  end  
  | and_exp      => match stack with
                 | n1 :: n2 :: stack' => ( andb n1 n2) :: stack'
                 | _ => stack
                 end 
  | or_exp       => match stack with
                 | n1 :: n2 :: stack' => ( orb n1 n2) :: stack'
                 | _ => stack
                 end
  end.


Fixpoint run_instructions (is' : list Instruction)
         (env : EnvB) (stack : Stack) : Stack :=
  match is' with
  | [] => stack
  | i :: is'' => run_instructions is'' env (run_instruction i env stack)
  end.


Fixpoint compile (e : BExp1) : list Instruction :=
  match e with
  | b_True  => [push_const true]
  | b_False => [push_const false]
  | b_Var x => [push_var x]
  | b_Not x => (compile x ) ++ [not_exp]
  | b_And e1 e2 => (compile e1) ++ (compile e2) ++ [and_exp]
  | b_Or e1 e2 => (compile e1) ++ (compile e2) ++ [or_exp]
  end.

Lemma soundness_helper :
  forall e env stack is',
    run_instructions (compile e ++ is') env stack =
    run_instructions is' env ((interpret e env) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite IHe. simpl. reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite andb_comm.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite orb_comm.
    reflexivity.
Qed.

Theorem soundness :
  forall e env,
    run_instructions (compile e) env [] =
    [interpret e env].
Proof.
  intros.
  rewrite <- app_nil_r with (l := (compile e)).
  rewrite soundness_helper.
  simpl. trivial.
Qed.


