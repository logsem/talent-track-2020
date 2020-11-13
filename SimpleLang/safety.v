Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From SimpleLang Require Export dynamics. 

Lemma canonical_forms_nat : forall (v : expr) (Γ : TypeEnv.type_env), 
  val v -> typed Γ v TNat -> exists n, v = (Nat n).
Proof. Admitted.


Theorem progress : forall (e : expr) (t : type), 
  typed TypeEnv.empty e t ->
  val e \/ (exists e', step e e').
Proof. 
  intros e t H. induction H.
  (* Induction on typing relation *)
  (* Case: T_unit *)
  - left; simpl; apply I.
  (* Case: T_Var *)
  - (* saving that Gamma is empty? *) admit.
  (* Case: T_nat *)
  - left; simpl; apply I.
  (* Case: T_add *) 
  - right. destruct IHtyped1 as [He1_val | He1_step]. 
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val H).
        destruct (canonical_forms_nat e2 Γ He2_val H0).
        rewrite -> H1; rewrite -> H2.
        exists (Nat (x + x0)).
        constructor. (** aligns with E_add *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (add e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (add e1' e2).
      constructor; assumption.
  (* Case: T_sub *)
 
Admitted.

Theorem preservation : forall (Γ : TypeEnv.type_env) (e e' : expr) (t : type),
  typed Γ e t ->
  step e e' ->
  typed Γ e' t.
Proof. Admitted.