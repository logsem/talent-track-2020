Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From SimpleLang Require Export dynamics. 

Theorem progress : forall (e : expr) (t : type), 
  typed TypeEnv.empty e t ->
  val e \/ (exists  e', step e e').
Proof. Admitted.

Theorem preservation : forall (Γ : TypeEnv.type_env) (e e' : expr) (t : type),
  typed Γ e t ->
  step e e' ->
  typed Γ e' t.
Proof. Admitted.