Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From SimpleLang Require Export dynamics.

Lemma typed_inversion_nat : forall (e : expr) (t : type) (Γ : TypeEnv.type_env),
  typed Γ e t -> exists n, e = Nat n ->
    t = TNat.
Proof.
Admitted.

Lemma canonical_forms_nat : forall (v : expr) (Γ : TypeEnv.type_env), 
  val v -> typed Γ v TNat -> exists n, v = (Nat n).
Proof.
  intros v Γ Hv_val Hv_TNat. destruct v; try contradiction.
  - admit. (* How to prove that [typed Γ unit TNat] is a contradiction? *)
  - exists n; reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma canonical_forms_bool : forall (v : expr) (Γ : TypeEnv.type_env), 
  val v -> typed Γ v TBool -> exists b, v = (Bool b).
Proof. Admitted.

Lemma canonical_forms_sum : forall (v : expr) (t1 t2 : type) (Γ : TypeEnv.type_env), 
  val v -> typed Γ v (TSum t1 t2) ->
    exists v', val v' /\ (v = (inj1 v') \/ v = (inj2 v')).
(** maybe? *)
Proof. Admitted.

Lemma canonical_forms_prod : forall (v : expr) (t1 t2 : type) (Γ : TypeEnv.type_env), 
  val v -> typed Γ v (TProd t1 t2) ->
    exists v1 v2, val v1 /\ val v2 /\ v = pair v1 v2.
Proof. Admitted.

Lemma canonical_forms_fun : forall (v : expr) (t1 t2 : type) (Γ : TypeEnv.type_env), 
  val v -> typed Γ v (TFun t1 t2) ->
    exists e, v = rec e.
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
  - right. destruct IHtyped1 as [He1_val | He1_step]. 
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val H).
        destruct (canonical_forms_nat e2 Γ He2_val H0).
        rewrite -> H1; rewrite -> H2.
        exists (Nat (x - x0)).
        constructor. (** aligns with E_sub *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (sub e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (sub e1' e2).
      constructor; assumption.

  (* Case: T_mul *)
  - right. destruct IHtyped1 as [He1_val | He1_step]. 
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val H).
        destruct (canonical_forms_nat e2 Γ He2_val H0).
        rewrite -> H1; rewrite -> H2.
        exists (Nat (x * x0)).
        constructor. (** aligns with E_mul *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (mul e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (mul e1' e2).
      constructor; assumption.

  (* Case: T_le *)
  - right. destruct IHtyped1 as [He1_val | He1_step]. 
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val H).
        destruct (canonical_forms_nat e2 Γ He2_val H0).
        rewrite -> H1; rewrite -> H2.
        exists (Bool (x <=? x0)).
        constructor. (** aligns with E_le *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (le e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (le e1' e2).
      constructor; assumption.

  (* Case: T_lt *)
  - right. destruct IHtyped1 as [He1_val | He1_step]. 
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val H).
        destruct (canonical_forms_nat e2 Γ He2_val H0).
        rewrite -> H1; rewrite -> H2.
        exists (Bool (x <? x0)).
        constructor. (** aligns with E_lt *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (lt e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (lt e1' e2).
      constructor; assumption.

  (* Case: T_eq *)
  - right. destruct IHtyped1 as [He1_val | He1_step]. 
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val H).
        destruct (canonical_forms_nat e2 Γ He2_val H0).
        rewrite -> H1; rewrite -> H2.
        exists (Bool (x =? x0)).
        constructor. (** aligns with E_eq *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (eq e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (eq e1' e2).
      constructor; assumption.

  (* Case: T_Bool *)
  - left; simpl; apply I. 

  (* Case: T_if *)
  - right. destruct IHtyped1 as [He1_val | He1_step].
    (* e1 is a value *)
    + destruct (canonical_forms_bool e1 Γ He1_val H).
      destruct x.
      (* e1 is true *)
      * rewrite H2. exists e2. constructor.
      (* e1 is false *)
      * rewrite H2. exists e3. constructor.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (ifthenelse e1' e2 e3).
      constructor; assumption.

  (* Case: T_pair *)
  - destruct IHtyped1 as [He1_val | He1_step].
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value) *)
      * left. simpl. split; assumption.
      (* e2 takes a step (and e1 is a value) *)
      * right. destruct He2_step as [e2'].
        exists (pair e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + right. destruct He1_step as [e1'].
      exists (pair e1' e2).
      constructor; assumption.

  (* Case: T_fst *)
  - right. destruct IHtyped as [He_val | He_step].
    (* e is a value *)
    + destruct (canonical_forms_prod e t1 t2 Γ He_val H) as [v1].
      destruct H0 as [v2]. destruct H0; destruct H1.
      rewrite H2. exists v1.
      constructor; assumption.
    (* e takes a step *)
    + destruct He_step as [e'].
      exists (fst e').
      constructor; assumption.

  (* Case: T_snd *)
  - right. destruct IHtyped as [He_val | He_step].
    (* e is a value *)
    + destruct (canonical_forms_prod e t1 t2 Γ He_val H) as [v1].
      destruct H0 as [v2]. destruct H0; destruct H1.
      rewrite H2. exists v2.
      constructor; assumption.
    (* e takes a step *)
    + destruct He_step as [e'].
      exists (snd e').
      constructor; assumption.

  (* Case: T_inj1 *)
  - destruct IHtyped as [He_val | He_step].
    (* e is a value *)
    + left. simpl. apply He_val.
    (* e takes a step *)
    + right. destruct He_step as [e'].
      exists (inj1 e'). 
      constructor; assumption.

  (* Case: T_inj2 *)
  - destruct IHtyped as [He_val | He_step].
    (* e is a value *)
    + left. simpl. apply He_val.
    (* e takes a step *)
    + right. destruct He_step as [e'].
      exists (inj2 e'). 
      constructor; assumption.

  (* Case: T_match *)
  - right. destruct IHtyped1 as [He1_val | He1_step].
    (* e1 is a value *)
    + destruct (canonical_forms_sum e1 t1 t2 Γ He1_val H) as [v].
      destruct H2. destruct H3 as [He1_inj1 | He1_inj2].
      (* e1 is inj1 v *)
      * rewrite He1_inj1. exists (subst e2 0 v).
        constructor; assumption.
      (* e1 is inj2 v *)
      * rewrite He1_inj2. exists (subst e3 0 v).
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. 
      exists (matchwith e1' e2 e3).
      constructor; assumption.

  (* Case: T_rec *)
  - destruct IHtyped as [He_val | He_step];
    left; simpl; apply I.

  (* Case: T_app *)
  - right. destruct IHtyped1 as [He1_val | He1_step].
    (* e1 is a value *)
    + destruct IHtyped2 as [He2_val | He2_step].
      (* e2 is a value (and e1 is a value) *)
      * destruct (canonical_forms_fun e1 t1 t2 Γ He1_val H) as [e].
        exists (subst (subst e 0 e1) 1 e2).
        rewrite H1; constructor; assumption.
      (* e2 takes a step (and e1 is a value) *)
      * destruct He2_step as [e2'].
        exists (app e1 e2').
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1'].
      exists (app e1' e2).
      constructor; assumption.
Admitted.

Theorem preservation : forall (Γ : TypeEnv.type_env) (e e' : expr) (t : type),
  typed Γ e t ->
  step e e' ->
  typed Γ e' t.
Proof. Admitted.