From SimpleLang Require Export statics.

Require Import Coq.Arith.PeanoNat.

(* SUBSTITUTION *)
(** helper function: shift *)
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
  | ifthenelse e1 e2 e3 => ifthenelse (shift i j e1) (shift i j e2) (shift i j e2)
  
  (* products *)
  | pair e1 e2 => pair (shift i j e1) (shift i j e2)
  | fst e1 => fst (shift i j e1)
  | snd e1 => snd (shift i j e1)
  
  (* sums *)
  | inj1 e1 => inj1 (shift i j e1)
  | inj2 e1 => inj2 (shift i j e1)
  | matchwith e1 e2 e3 => matchwith (shift i j e1) (shift (i+1) j e2) (shift (i+1) j e3)

  (* recursive functions *)
  | rec e1 => rec (shift (i+2) j e1)
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
  | ifthenelse e1 e2 e3 => ifthenelse (subst e1 i s) (subst e2 i s) (subst e3 i s)

  (* products *)
  | pair e1 e2 => pair (subst e1 i s) (subst e2 i s)
  | fst e1 => fst (subst e1 i s)
  | snd e1 => snd (subst e1 i s)

  (* sums *)
  | inj1 e1 => inj1 (subst e1 i s)
  | inj2 e1 => inj2 (subst e1 i s)
  | matchwith e1 e2 e3 => matchwith (subst e1 i s) (subst e2 (i+1) (shift 0 1 s)) (subst e3 (i+1) (shift 0 1 s))

  (* recursive functions *)
  | rec e1 => rec (subst e1 (i+2) (shift 0 2 s))
  | app e1 e2 => app (subst e1 i s) (subst e2 i s)
  end
.


(* OPERATIONAL SEMANTICS *)
(*TODO*)