Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From SimpleLang Require Export dynamics.

Lemma canonical_forms_nat (v : expr) (Γ : TypeEnv.type_env) :
  val v -> typed Γ v TNat -> exists n, v = (Nat n).
Proof.
  intros Hv Hvt.
  destruct v; inversion Hvt; subst; simpl in *; try contradiction; eauto.
Qed.

Lemma canonical_forms_bool (v : expr) (Γ : TypeEnv.type_env) :
  val v -> typed Γ v TBool -> exists b, v = (Bool b).
Proof.
  intros Hv Hvt.
  destruct v; inversion Hvt; subst; simpl in *; try contradiction; eauto.
Qed.

Lemma canonical_forms_sum (v : expr) (t1 t2 : type) (Γ : TypeEnv.type_env) :
  val v -> typed Γ v (TSum t1 t2) ->
    exists v', val v' /\ (v = (inj1 v') \/ v = (inj2 v')).
Proof.
  intros Hv Hvt.
  destruct v; inversion Hvt; subst; simpl in *; try contradiction; eauto.
Qed.

Lemma canonical_forms_prod (v : expr) (t1 t2 : type) (Γ : TypeEnv.type_env) :
  val v -> typed Γ v (TProd t1 t2) ->
    exists v1 v2, val v1 /\ val v2 /\ v = pair v1 v2.
Proof.
  intros Hv Hvt.
  destruct v; inversion Hvt; subst; simpl in *; try contradiction;
    destruct Hv; eauto.
Qed.

Lemma canonical_forms_fun (v : expr) (t1 t2 : type) (Γ : TypeEnv.type_env) :
  val v -> typed Γ v (TFun t1 t2) -> exists e, v = rec e.
Proof.
  intros Hv Hvt.
  inversion Hvt; subst; simpl in *; try contradiction; eauto.
Qed.

Theorem progress (e : expr) (t : type) :
  typed TypeEnv.empty e t -> val e \/ (exists e', step e e').
Proof.
  intros Het. remember TypeEnv.empty as Γ. induction Het.
  (* Induction on typing relation *)

  (* Case: T_unit *)
  - left; simpl; trivial.

  (* Case: T_var *)
  - rewrite HeqΓ in H. apply nth_error_In in H. contradiction.

  (* Case: T_nat *)
  - left; simpl; trivial.

  (* Case: T_add *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val); [trivial|].
        destruct (canonical_forms_nat e2 Γ He2_val); [trivial|].
        subst.
        eexists (Nat (_ + _)).
        constructor. (** aligns with E_add *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (add e1 e2').
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (add e1' e2).
      constructor; assumption.

  (* Case: T_sub *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val); [trivial|].
        destruct (canonical_forms_nat e2 Γ He2_val); [trivial|].
        subst.
        eexists (Nat (_ - _)).
        constructor. (** aligns with E_sub *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (sub e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (sub e1' e2).
      constructor; assumption.

  (* Case: T_mul *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val); [trivial|].
        destruct (canonical_forms_nat e2 Γ He2_val); [trivial|].
        subst.
        eexists (Nat (_ * _)).
        constructor. (** aligns with E_mul *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (mul e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (mul e1' e2).
      constructor; assumption.

  (* Case: T_le *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |]. 
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val); [trivial|].
        destruct (canonical_forms_nat e2 Γ He2_val); [trivial|].
        subst.
        eexists (Bool (_ <=? _)).
        constructor. (** aligns with E_le *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (le e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (le e1' e2).
      constructor; assumption.

  (* Case: T_lt *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |]. 
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val); [trivial|].
        destruct (canonical_forms_nat e2 Γ He2_val); [trivial|].
        subst.
        eexists (Bool (_ <? _)).
        constructor. (** aligns with E_lt *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (lt e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (lt e1' e2).
      constructor; assumption.

  (* Case: T_eq *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |]. 
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value)*)
      * destruct (canonical_forms_nat e1 Γ He1_val); [trivial|].
        destruct (canonical_forms_nat e2 Γ He2_val); [trivial|].
        subst.
        eexists (Bool (_ =? _)).
        constructor. (** aligns with E_eq *)
      (* e2 takes a step (and e1 is a value)*)
      * destruct He2_step as [e2']. exists (eq e1 e2'). 
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (eq e1' e2).
      constructor; assumption.

  (* Case: T_Bool *)
  - left; simpl; trivial. 

  (* Case: T_if *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct (canonical_forms_bool e1 Γ He1_val) as [b]; [trivial|].
      subst. destruct b.
      (* e1 is true *)
      * exists e2; constructor.
      (* e1 is false *)
      * exists e3; constructor.
    (* e1 takes a step *)
    + destruct He1_step as [e1']. exists (ifthenelse e1' e2 e3).
      constructor; assumption.

  (* Case: T_pair *)
  - destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
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
  - right. destruct IHHet as [He_val | He_step]; [trivial| |].
    (* e is a value *)
    + destruct (canonical_forms_prod e t1 t2 Γ He_val) as [v1 [v2 [Hv1_val [Hv2_val He_v1v2]]]]; [trivial|].
      subst. exists v1.
      constructor; assumption.
    (* e takes a step *)
    + destruct He_step as [e'].
      exists (fst e').
      constructor; assumption.

  (* Case: T_snd *)
  - right. destruct IHHet as [He_val | He_step]; [trivial| |].
    (* e is a value *)
    + destruct (canonical_forms_prod e t1 t2 Γ He_val) as [v1 [v2 [Hv1_val [Hv2_val He_v1v2]]]]; [trivial|].
      subst. exists v2.
      constructor; assumption.
    (* e takes a step *)
    + destruct He_step as [e'].
      exists (snd e').
      constructor; assumption.

  (* Case: T_inj1 *)
  - destruct IHHet as [He_val | He_step]; [trivial| |].
    (* e is a value *)
    + left. simpl. apply He_val.
    (* e takes a step *)
    + right. destruct He_step as [e'].
      exists (inj1 e'). 
      constructor; assumption.

  (* Case: T_inj2 *)
  - destruct IHHet as [He_val | He_step]; [trivial| |].
    (* e is a value *)
    + left. simpl. apply He_val.
    (* e takes a step *)
    + right. destruct He_step as [e'].
      exists (inj2 e'). 
      constructor; assumption.

  (* Case: T_match *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct (canonical_forms_sum e1 t1 t2 Γ He1_val) as [v [Hv_val [He1_inj1 | He1_inj2]]]; [trivial| |].
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
  - left. simpl; trivial.

  (* Case: T_app *)
  - right. destruct IHHet1 as [He1_val | He1_step]; [trivial| |].
    (* e1 is a value *)
    + destruct IHHet2 as [He2_val | He2_step]; [trivial| |].
      (* e2 is a value (and e1 is a value) *)
      * destruct (canonical_forms_fun e1 t1 t2 Γ He1_val) as [e]; [trivial|].
        exists (subst (subst e 0 e1) 1 e2).
        subst.
        constructor; assumption.
      (* e2 takes a step (and e1 is a value) *)
      * destruct He2_step as [e2'].
        exists (app e1 e2').
        constructor; assumption.
    (* e1 takes a step *)
    + destruct He1_step as [e1'].
      exists (app e1' e2).
      constructor; assumption.
Qed.

Theorem preservation : forall (Γ : TypeEnv.type_env) (e e' : expr) (t : type),
  typed Γ e t ->
  step e e' ->
  typed Γ e' t.
Proof.
  intros Γ e e' t Het. revert e'.
  induction Het; intros e' He_step.
  (* Induction on typing relation *)

  (* Case: T_unit *)
  - inversion He_step.
  
  (* Case: T_Var *)
  - inversion He_step.

  (* Case: T_nat *)
  - inversion He_step.

  (* Case: T_add *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)    
    + constructor; [trivial|]. apply IHHet2; assumption.
    (* e1 and e2 are Nat n *)
    + constructor.

  (* Case: T_sub *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)    
    + constructor; [trivial|]. apply IHHet2; assumption.
    (* e1 and e2 are Nat n *)
    + constructor.

  (* Case: T_mul *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)    
    + constructor; [trivial|]. apply IHHet2; assumption.
    (* e1 and e2 are Nat n *)
    + constructor.

  (* Case: T_le *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)    
    + constructor; [trivial|]. apply IHHet2; assumption.
    (* e1 and e2 are Nat n *)
    + constructor.

  (* Case: T_lt *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)    
    + constructor; [trivial|]. apply IHHet2; assumption.
    (* e1 and e2 are Nat n *)
    + constructor.

  (* Case: T_eq *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)    
    + constructor; [trivial|]. apply IHHet2; assumption.
    (* e1 and e2 are Nat n *)
    + constructor.

  (* Case: T_bool *)
  - inversion He_step.

  (* Case: T_if *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial|trivial]. apply IHHet1; assumption.
    (* e1 is true *)
    + subst; assumption.
    (* e1 is false *)
    + subst; assumption.

  (* Case: T_pair *)
  - inversion He_step.
    (* e1 takes a step *)
    + constructor; [|trivial]. apply IHHet1; assumption.
    (* e1 is a value and e2 takes a step *)
    + constructor; [trivial|]. apply IHHet2; assumption.

  (* Case: T_fst *)
  - inversion He_step.
    (* e takes a step *)
    + econstructor. apply IHHet; assumption.
    (* e is pair v1 v2 *)
    + admit.

  (* Case: T_snd *)
  - inversion He_step.
    (* e takes a step *)
    + econstructor. apply IHHet; assumption.
    (* e is pair v1 v2 *)
    + admit.

  (* Case: T_inj1 *)
  - inversion He_step.
    constructor. apply IHHet; assumption.

  (* Case: T_inj2 *)
  - inversion He_step.
    constructor. apply IHHet; assumption.

  (* Case: T_match *)
  - inversion He_step.
    + econstructor; [|eauto|eauto]. apply IHHet1; assumption.
    + apply subst_lemma with (Γ1:=[]) (t':=t1); simpl.
      * assumption.
      * admit.
    + admit.
Admitted.
