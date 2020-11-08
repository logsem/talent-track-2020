Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From SimpleLang Require Export statics.

(* SUBSTITUTION *)
(** helper function: shift 
    in for all variables in e with index under i, add j to i *)
Fixpoint shift (i j : nat) (e : expr) : expr :=
match e with
  | unit => unit
  | Var n => if (n <? i) then (Var n) else (Var (n+j))
  
  (*numbers*)
  | Nat n => Nat n
  | add e1 e2 => add (shift i j e1) (shift i j e2)
  | sub e1 e2 => sub (shift i j e1) (shift i j e2)
  | mul e1 e2 => mul (shift i j e1) (shift i j e2)
  | le e1 e2 => le (shift i j e1) (shift i j e2)
  | lt e1 e2 => lt (shift i j e1) (shift i j e2)
  | eq e1 e2 => eq (shift i j e1) (shift i j e2)
  
  (* booleans *)
  | Bool b => Bool b
  | ifthenelse e1 e2 e3 => ifthenelse (shift i j e1) (shift i j e2) (shift i j e3)
  
  (* products *)
  | pair e1 e2 => pair (shift i j e1) (shift i j e2)
  | fst e1 => fst (shift i j e1)
  | snd e1 => snd (shift i j e1)
  
  (* sums *)
  | inj1 e1 => inj1 (shift i j e1)
  | inj2 e1 => inj2 (shift i j e1)
  | matchwith e1 e2 e3 => matchwith (shift i j e1) (shift (S i) j e2) (shift (S i) j e3)

  (* recursive functions *)
  | rec e1 => rec (shift (S (S i)) j e1)
  | app e1 e2 => app (shift i j e1) (shift i j e2)
end
.

(** in expression e substitute variable i with s *)
Fixpoint subst (e : expr) (i : id) (s : expr) : expr :=
  match e with
  | unit => unit
  | Var n => if (i =? n) then s else (if (n <? i) then (Var n) else (Var (n-1)))

  (* numbers *)
  | Nat n => Nat n
  | add e1 e2 => add (subst e1 i s) (subst e2 i s)
  | sub e1 e2 => sub (subst e1 i s) (subst e2 i s)
  | mul e1 e2 => mul (subst e1 i s) (subst e2 i s)
  | le e1 e2 => le (subst e1 i s) (subst e2 i s)
  | lt e1 e2 => lt (subst e1 i s) (subst e2 i s)
  | eq e1 e2 => eq (subst e1 i s) (subst e2 i s)

  (* booleans *)
  | Bool b => Bool b
  | ifthenelse e1 e2 e3 =>
    ifthenelse (subst e1 i s) (subst e2 i s) (subst e3 i s)

  (* products *)
  | pair e1 e2 => pair (subst e1 i s) (subst e2 i s)
  | fst e1 => fst (subst e1 i s)
  | snd e1 => snd (subst e1 i s)

  (* sums *)
  | inj1 e1 => inj1 (subst e1 i s)
  | inj2 e1 => inj2 (subst e1 i s)
  | matchwith e1 e2 e3 =>
    matchwith
      (subst e1 i s)
      (subst e2 (i+1) (shift 0 1 s)) (subst e3 (i+1) (shift 0 1 s))

  (* recursive functions *)
  | rec e1 => rec (subst e1 (i+2) (shift 0 2 s))
  | app e1 e2 => app (subst e1 i s) (subst e2 i s)
  end
.


Lemma shift_0 : forall (i : nat) (e : expr),
  shift i 0 e = e.
Proof.
  intros. generalize i as i'. induction e; intros i'; simpl;
  try rewrite IHe; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3;
  try reflexivity.
  - (* Var *) destruct (x <? i').
    + reflexivity.
    + rewrite Nat.add_comm. reflexivity.
Qed.

Lemma shift_lemma : forall (Gamma1 Gamma2 Delta : TypeEnv.type_env) (t : type) (e : expr),
  typed (Gamma1 ++ Gamma2) e t ->
  typed (Gamma1 ++ Delta ++ Gamma2) (shift (length Gamma1) (length Delta) e) t.
Proof.
  intros Γ1 Γ2 Δ t e Het.
  remember (Γ1 ++ Γ2) as Ξ.
  revert Γ1 Γ2 HeqΞ.
  induction Het; simpl; intros Γ1 Γ2 HeqΞ.
  - constructor.
  - simpl. destruct (x <? length Γ1) eqn:Hx; rewrite HeqΞ in H;
    constructor; unfold TypeEnv.lookup in *.
    + replace (nth_error (Γ1 ++ Δ ++ Γ2) x) with (nth_error Γ1 x).
      * rewrite <- H. replace (nth_error (Γ1 ++ Γ2) x) with (nth_error Γ1 x).
        -- reflexivity.
        -- symmetry. apply nth_error_app1. apply Nat.ltb_lt.
           apply Hx.
      * symmetry. apply nth_error_app1. apply Nat.ltb_lt.
        apply Hx.
    + replace (nth_error (Γ1 ++ Δ ++ Γ2) (x + length Δ)) with (nth_error (Δ ++ Γ2) (x + length Δ - length Γ1));
      apply Nat.ltb_ge in Hx.
      * rewrite <- H. replace (nth_error (Γ1 ++ Γ2) x) with (nth_error Γ2 (x - length Γ1)).
        -- replace (nth_error (Δ ++ Γ2) (x + length Δ - length Γ1)) with (nth_error (Γ2) (x + length Δ - length Γ1 - length Δ)).
           ++ rewrite <- Nat.sub_add_distr. rewrite Nat.add_comm with (n:=(length Γ1)).
              rewrite Nat.sub_add_distr. rewrite Nat.add_sub.
              reflexivity. (* How can this be done more easily? *)
           ++ symmetry. apply nth_error_app2. apply Nat.le_add_le_sub_l.
              apply Nat.add_le_mono_r. apply Hx.
        -- symmetry. apply nth_error_app2. apply Hx.
      * symmetry. apply nth_error_app2.
        apply Plus.le_plus_trans. apply Hx.
  - simpl. constructor.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; constructor.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; econstructor; eauto.
  - simpl; econstructor; eauto.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; econstructor.
    + apply IHHet1; trivial.
    + apply (IHHet2 (t1 :: Γ1)).
      rewrite HeqΞ; reflexivity.
    + apply (IHHet3 (t2 :: Γ1)).
      rewrite HeqΞ; reflexivity.
  - constructor.
    apply (IHHet (_ :: _ :: _)).
    rewrite HeqΞ; reflexivity.
  - econstructor; eauto.
Qed.

Lemma subst_lemma : forall (Gamma1 Gamma2 : TypeEnv.type_env) (t t' : type) (e e' : expr),
  typed (Gamma1 ++ t' :: Gamma2) e t ->
  typed (Gamma1 ++ Gamma2) e' t' ->
  typed (Gamma1 ++ Gamma2) (subst e (length Gamma1) e') t.
Proof.

Admitted.


(* OPERATIONAL SEMANTICS *)
Inductive eval : expr -> expr -> Prop :=
  (* numbers *)
  (** add **)
  | E_add1 e1 e2 e1' :
      eval e1 e1' ->
      eval (add e1 e2) (add e1' e2)
  | E_add2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (add v1 e2) (add v1 e2')
  | E_add n1 n2 :
      eval (add (Nat n1) (Nat n2)) (Nat (n1 + n2))
  (** sub **)
  | E_sub1 e1 e2 e1' :
      eval e1 e1' ->
      eval (sub e1 e2) (sub e1' e2)
  | E_sub2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (sub v1 e2) (sub v1 e2')
  | E_sub n1 n2 :
      eval (sub (Nat n1) (Nat n2)) (Nat (n1 - n2))
  (** mul **) 
  | E_mul1 e1 e2 e1' :
      eval e1 e1' ->
      eval (mul e1 e2) (mul e1' e2)
  | E_mul2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (mul v1 e2) (mul v1 e2')
  | E_mul n1 n2 :
      eval (mul (Nat n1) (Nat n2)) (Nat (n1 * n2))
  (** le **)
  | E_le1 e1 e2 e1' :
      eval e1 e1' ->
      eval (le e1 e2) (le e1' e2)
  | E_le2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (le v1 e2) (le v1 e2')
  | E_le n1 n2 :
      eval (le (Nat n1) (Nat n2)) (Bool (n1 <=? n2))
  (** lt **)
  | E_lt1 e1 e2 e1' :
      eval e1 e1' ->
      eval (lt e1 e2) (lt e1' e2)
  | E_lt2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (lt v1 e2) (lt v1 e2')
  | E_lt n1 n2 :
      eval (lt (Nat n1) (Nat n2)) (Bool (n1 <? n2))
  (** eq **)
  | E_eq1 e1 e2 e1' :
      eval e1 e1' ->
      eval (eq e1 e2) (eq e1' e2)
  | E_eq2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (eq v1 e2) (eq v1 e2')
  | E_eq n1 n2 :
      eval (eq (Nat n1) (Nat n2)) (Bool (n1 =? n2))

  (* booleans *)
  | E_if e1 e2 e3 e1' :
      eval e1 e1' ->
      eval (ifthenelse e1 e2 e3) (ifthenelse e1' e2 e3)
  | E_if_true e2 e3 :
      eval (ifthenelse (Bool true) e2 e3) e2
  | E_if_false e2 e3 :
      eval (ifthenelse (Bool false) e2 e3) e3
  
  (* products *)
  | E_pair1 e1 e2 e1' :
      eval e1 e1' ->
      eval (pair e1 e2) (pair e1' e2)
  | E_pair2 v1 e2 e2' :
      val v1 ->
      eval e2 e2' ->
      eval (pair v1 e2) (pair v1 e2')
  (** fst **)
  | E_fst1 e1 e1' :
      eval e1 e1' ->
      eval (fst e1) (fst e1')
  | E_fst v1 v2 :
      val v1 ->
      val v2 ->
      eval (fst (pair v1 v2)) v1
  (** snd **)
  | E_snd1 e1 e1' :
      eval e1 e1' ->
      eval (snd e1) (snd e1')
  | E_snd v1 v2 :
      val v1 ->
      val v2 ->
      eval (snd (pair v1 v2)) v2

  (* sums *)
  | E_inj1 e e' :
      eval e e' ->
      eval (inj1 e) (inj1 e')
  | E_inj2 e e' :
      eval e e' ->
      eval (inj2 e) (inj2 e')
  (** match **)
  | E_match e1 e2 e3 e1' :
      eval e1 e1' ->
      eval (matchwith e1 e2 e3) (matchwith e1' e2 e3)
  | E_match_inj1 v e2 e3 :
      val v ->
      eval (matchwith (inj1 v) e2 e3) (subst e2 0 v)
  | E_match_inj2 v e2 e3 :
      val v ->
      eval (matchwith (inj2 v) e2 e3) (subst e3 0 v)

  (* recursive_functions *)
  | E_app1 e1 e2 e1':
      eval e1 e1' ->
      eval (app e1 e2) (app e1' e2)
  | E_app2 v1 e2 e2':
      val v1 ->
      eval e2 e2' ->
      eval (app v1 e2) (app v1 e2')
  | E_app e v :
      val v ->
      eval (app (rec e) v) (subst (subst e 0 (rec e)) 1 v) (* FIXME Lasse: Was 0 the fuction or the param? *)
                                                           (* FIXME Stinna: I'm unsure about the evaluated expression, (subst ...) *)
.

Example two_plus_two_four : eval (add (Nat 2) (Nat 2)) (Nat 4).
Proof.
  apply E_add.
Qed.

Example two_minus_one_plus_three : eval (add (sub (Nat 2) (Nat 1)) (Nat 3)) (add (Nat 1) (Nat 3)).
Proof.
  apply E_add1. (** e1 --> e1' implies e1 + e2 --> e1' + e2 by add1
                    Which means if we can prove  e1 --> e1', we are done, so we apply add1. **)
  apply E_sub.  (** and e1 --> e1' is true by sub **)
Qed.

Definition fac := rec ( ifthenelse (eq (Var 1) (Nat 0)) (Nat 1) (mul (Var 1) (app (Var 0) (sub (Var 1) (Nat 1)))) ).
Example fac_five_120 : eval (app fac (Nat 5)) (Nat 120).
Proof.
  (* FIXME Lasse: Help! *)
  (* FIXME Stinna: also help! Is fac_five_120 not of the form in E_app?
                   i.e. fac is (rec f(x) := e) and (Nat 5) is a value v *)
Admitted.




