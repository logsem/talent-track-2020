Require Import Coq.Lists.List.


(* -- SYNTAX  -- *)
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

Inductive typed (Γ : TypeEnv.type_env) : expr -> type -> Prop :=
  | T_unit : typed Γ unit TUnit
  | T_var (x : id) (t : type) :
      TypeEnv.lookup Γ x = Some t ->
      typed Γ (Var x) t

  (* numbers *)
  | T_nat (n : nat) : typed Γ (Nat n) TNat
  | T_add (e1 e2 : expr) : 
      typed Γ e1 TNat ->
      typed Γ e2 TNat ->
      typed Γ (add e1 e2) TNat
  | T_sub (e1 e2 : expr) : 
      typed Γ e1 TNat ->
      typed Γ e2 TNat ->
      typed Γ (sub e1 e2) TNat
  | T_mul (e1 e2 : expr) : 
      typed Γ e1 TNat ->
      typed Γ e2 TNat ->
      typed Γ (mul e1 e2) TNat
  | T_le (e1 e2 : expr) : 
      typed Γ e1 TNat ->
      typed Γ e2 TNat ->
      typed Γ (le e1 e2) TBool
  | T_lt (e1 e2 : expr) : 
      typed Γ e1 TNat ->
      typed Γ e2 TNat ->
      typed Γ (lt e1 e2) TBool
  | T_eq (e1 e2 : expr) : 
      typed Γ e1 TNat ->
      typed Γ e2 TNat ->
      typed Γ (eq e1 e2) TBool

  (* booleans*)
  | T_bool (b : bool) : typed Γ (Bool b) TBool
  | T_if (e1 e2 e3 : expr) (t : type) : 
      typed Γ e1 TBool ->
      typed Γ e2 t ->
      typed Γ e3 t ->
      typed Γ (ifthenelse e1 e2 e3) t

  (* products *)
  | T_pair (e1 e2 : expr) (t1 t2 : type) :
      typed Γ e1 t1 ->
      typed Γ e2 t2 ->
      typed Γ (pair e1 e2) (TProd t1 t2)
  | T_fst (e : expr) (t1 t2 : type) :
      typed Γ e (TProd t1 t2) ->
      typed Γ (fst e) t1
  | T_snd (e : expr) (t1 t2 : type) :
      typed Γ e (TProd t1 t2) ->
      typed Γ (snd e) t2

  (* sums *)
  | T_inj1 (e : expr) (t1 t2 : type) :
      typed Γ e t1 ->
      typed Γ (inj1 e) (TSum t1 t2)
  | T_inj2 (e : expr) (t1 t2 : type) :
      typed Γ e t2 ->
      typed Γ (inj2 e) (TSum t1 t2)
  | T_match (e1 e2 e3 : expr) (t1 t2 t : type) :
      typed Γ e1 (TSum t1 t2) ->
      typed (TypeEnv.add t1 Γ) e2 t ->
      typed (TypeEnv.add t2 Γ) e3 t ->
      typed Γ (matchwith e1 e2 e3) t

  (* recursive functions *)
  | T_rec (e : expr) (t1 t2 : type) :
      typed (TypeEnv.add (TFun t1 t2) (TypeEnv.add t1 Γ)) e t2 ->
      typed Γ (rec e) (TFun t1 t2)
  | T_app (e1 e2 : expr) (t1 t2 : type) :
      typed Γ e1 (TFun t1 t2) ->
      typed Γ e2 t1 ->
      typed Γ (app e1 e2) t2
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