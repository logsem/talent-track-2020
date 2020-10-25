Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint nth_error {X : Type} (l : list X) (n : nat) (** from the Poly-chapter in our Coq-book**)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.


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
  | div (e1 e2 : expr)
  | le (e1 e2 : expr)
  | lt (e1 e2 : expr)
  | eq (e1 e2 : expr)

  (* booleans *)
  | True (** possibly a bad name? **)
  | False
  | ifthenelse (e1 e2 e3 : expr) (** TODO help - if then else already defined in Coq **)

  (* products *)
  | pair (e1 e2 : expr)
  | fst (e : expr)
  | snd (e : expr)

  (* sums *)
  | inj1 (e : expr)
  | inj2 (e : expr)
  | matchwith (e x : expr)(** TODO help - match e with inj1 x => e | inj2 x => e end **)

  (* recursive functions *)
  | rec (e : expr) (** not quite sure about this *)
.

(** VALUES *)
Inductive val :=
  | unit_val
  | Nat_val (n : nat)
  | pair_val (v1 v2 : val)
  | inj1_val (v : val)
  | inj2_val (v : val)
  | rec_val (e : expr)
.

(** TYPES *)
Inductive type :=
  | Unit
  | TNat
  | Bool
  | Prod (t1 t2 : type)
  | Sum (t1 t2 : type)
  | Fun (t1 t2 : type)
.

(* TYPING *)
Inductive typed (Gamma : list type) : expr -> type -> Prop :=
  | T_unit : typed Gamma unit Unit
  | T_Var (x : id) (t : type) :
      (*nth_error Gamma x = Some t -> (* TODO define nth_error function *)*)
      typed Gamma (Var x) t

  (* numbers *)
  | T_int (n : nat) : typed Gamma (Nat n) TNat
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
  | T_div (e1 e2 : expr) : 
      typed Gamma e1 TNat ->
      typed Gamma e2 TNat ->
    typed Gamma (div e1 e2) TNat
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
  | T_true : typed Gamma True Bool
  | T_false : typed Gamma False Bool
  | T_if (e1 e2 e3 : expr) (t : type) : 
      typed Gamma e1 Bool ->
      typed Gamma e2 t ->
      typed Gamma e3 t

  (* products *)
  | T_pair (e1 e2 : expr) (t1 t2 : type) :
      typed Gamma e1 t1 ->
      typed Gamma e2 t2 ->
      typed Gamma (pair e1 e2) (Prod t1 t2)
  | T_fst (e : expr) (t1 t2 : type) :
      typed Gamma e (Prod t1 t2) ->
      typed Gamma (fst e) t1
  | T_snd (e : expr) (t1 t2 : type) :
      typed Gamma e (Prod t1 t2) ->
      typed Gamma (snd e) t2

  (* sums *)
  | T_inj1 (e : expr) (t1 t2 : type) :
      typed Gamma e t1 ->
      typed Gamma (inj1 e) (Sum t1 t2)
  | T_inj2 (e : expr) (t1 t2 : type) :
      typed Gamma e t2 ->
      typed Gamma (inj2 e) (Sum t1 t2)
  | T_match (e1 x e2 e3 : expr) (t t1 t2 : type) : (** NB! this is wrong! *) (*TODO*)
      typed Gamma e1 (Sum t1 t2) ->
      typed Gamma (inj1 x) t1 ->
      typed Gamma (inj2 x) t2 ->
      typed Gamma (*and x : t1 ???*) e2 t ->
      typed Gamma (*and x : t2 ???*) e3 t ->
      typed Gamma (matchwith e1 x) t

  (* recursive functions *)
  (* | T_rec TODO
  | T_app TODO *)
.