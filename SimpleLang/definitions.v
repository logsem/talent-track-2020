Require Import Coq.Lists.List.


(* SYNTAX *)
Definition id := nat.


(** EXPRESSIONS **)
Inductive expr :=
  | unit
  | Var (x : id)

  (* numbers *)
  | Nat (n : nat)
  | add (e1 e2 : expr)
  | sub (e1 e2 : expr)
  | mul (e1 e2 : expr)
  | le (e1 e2 : expr)
  | lt (e1 e2 : expr)
  | eq (e1 e2 : expr)

  (* booleans *)
  | Bool (b : bool)
  | ifthenelse (e1 e2 e3 : expr)

  (* products *)
  | pair (e1 e2 : expr)
  | fst (e : expr)
  | snd (e : expr)

  (* sums *)
  | inj1 (e : expr)
  | inj2 (e : expr)
  | matchwith (e1 e2 e3 : expr)

  (* recursive functions *)
  | rec (e : expr)
  | app (e1 e2 : expr)
.

(** VALUES **)
Fixpoint val (e : expr) : Prop :=
  match e with
  | unit | Nat _ | Bool _ | rec _ => True
  | pair v1 v2 => val v1 /\ val v2
  | inj1 v | inj2 v => val v
  | _ => False
  end.


(** TYPES *)
Inductive type :=
  | TUnit
  | TNat
  | TBool
  | TProd (t1 t2 : type)
  | TSum (t1 t2 : type)
  | TFun (t1 t2 : type)
.

(* TYPING *)
Module TypeEnv.
Definition type_env := list type.

Definition empty : type_env := nil.

Definition lookup : type_env -> id -> option type := @nth_error type.

Definition add : type -> type_env -> type_env := cons.
End TypeEnv.

Inductive typed (Gamma : TypeEnv.type_env) : expr -> type -> Prop :=
  | T_unit : typed Gamma unit TUnit
  | T_Var (x : id) (t : type) :
      TypeEnv.lookup Gamma x = Some t ->
      typed Gamma (Var x) t

  (* numbers *)
  | T_nat (n : nat) : typed Gamma (Nat n) TNat
  | T_add (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
      typed Gamma (add e1 e2) TNat
  | T_sub (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
      typed Gamma (sub e1 e2) TNat
  | T_mul (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
      typed Gamma (mul e1 e2) TNat
  | T_le (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
      typed Gamma (le e1 e2) TNat
  | T_lt (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
      typed Gamma (lt e1 e2) TNat
  | T_eq (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
      typed Gamma (eq e1 e2) TNat

  (* booleans*)
  | T_bool (b : bool) : typed Gamma (Bool b) TBool
  | T_if (e1 e2 e3 : expr) (t : type) : 
      typed Gamma e1 TBool ->
      typed Gamma e2 t ->
      typed Gamma e3 t ->
      typed Gamma (ifthenelse e1 e2 e3) t

  (* products *)
  | T_pair (e1 e2 : expr) (t1 t2 : type) :
      typed Gamma e1 t1 ->
      typed Gamma e2 t2 ->
      typed Gamma (pair e1 e2) (TProd t1 t2)
  | T_fst (e : expr) (t1 t2 : type) :
      typed Gamma e (TProd t1 t2) ->
      typed Gamma (fst e) t1
  | T_snd (e : expr) (t1 t2 : type) :
      typed Gamma e (TProd t1 t2) ->
      typed Gamma (snd e) t2

  (* sums *)
  | T_inj1 (e : expr) (t1 t2 : type) :
      typed Gamma e t1 ->
      typed Gamma (inj1 e) (TSum t1 t2)
  | T_inj2 (e : expr) (t1 t2 : type) :
      typed Gamma e t2 ->
      typed Gamma (inj2 e) (TSum t1 t2)
  | T_match (e1 e2 e3 : expr) (t1 t2 t : type) :
      typed Gamma e1 (TSum t1 t2) ->
      typed (TypeEnv.add t1 Gamma) e2 t ->
      typed (TypeEnv.add t2 Gamma) e3 t ->
      typed Gamma (matchwith e1 e2 e3) t

  (* recursive functions *)
  | T_rec (e : expr) (t1 t2 : type) :
      typed (TypeEnv.add (TFun t1 t2) (TypeEnv.add t1 Gamma)) e t2 ->
      typed Gamma (rec e) (TFun t1 t2)
  (* | T_app TODO *)
.

Example two_plus_two_TNat : typed TypeEnv.empty (add (Nat 2) (Nat 2)) TNat.
Proof.
  apply T_add.
  - apply T_nat.
  - apply T_nat.
Qed.

Example iftruethen3else5 : typed TypeEnv.empty (ifthenelse (Bool true) (Nat 3) (Nat 5)) TNat.
Proof.
  apply T_if.
  - apply T_bool.
  - apply T_nat.
  - apply T_nat.
Qed.