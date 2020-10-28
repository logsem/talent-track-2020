From SimpleLang Require Export statics.

(* SUBSTITUTION *)
(** in expression e substitute variable i with s *)
Fixpoint subst (e : expr) (i : id) (s : expr) : expr :=
  match e with
  | Unit => Unit
  (*TODO continue...*)
  end
.

(** helper function: shift *)
Fixpoint shift (i j : nat) (e : expr) : expr :=
match e with
  | Unit => Unit
  (*TODO continue*)
end.



(* OPERATIONAL SEMANTICS *)
(*TODO*)