From Stdlib Require Import List ZArith.
Import ListNotations.

Definition var := nat.

Definition vlt (x y : var) : Prop := Nat.lt x y.
Definition vle (x y : var) : Prop := Nat.le x y.
Definition vltb (x y : var) : bool := Nat.ltb x y.
Definition vleb (x y : var) : bool := Nat.leb x y.

Inductive primop : Type :=
  | Add : primop
  | Gt  : primop.

Inductive expr : Type :=
  | ValE    : val -> expr
  | SeqE    : eqn -> expr -> expr      (* eq; e *)
  | ExE     : var -> expr -> expr      (* Ex. e *)
  | FailE   : expr
  | ChoiceE : expr -> expr -> expr     (* e1 <|> e2  *)
  | AppE    : val -> val -> expr       (* v1 v2 (application) *)
  | OneE    : expr -> expr             (* one{e} *)
  | AllE    : expr -> expr             (* all{e} *)

with val : Type :=
  | VarV : var -> val
  | HnfV : hnf -> val

with hnf : Type :=
  | IntH : Z -> hnf
  | OpH  : primop -> hnf
  | TupH : list val -> hnf             (* <v1, ..., vn> *)
  | LamH : var -> expr -> hnf          (* \x. e *)

with eqn : Type :=
  | ExprEqn : expr -> eqn              (* plain expression as eqn *)
  | EqEqn   : val -> expr -> eqn.      (* v = e *)

(** A program is one{e} where e is closed. *)
Definition program := expr.

(** Coercions for conciseness. *)
Definition int_to_hnf (z : Z) : hnf := IntH z.
Definition op_to_hnf (op : primop) : hnf := OpH op.

Coercion VarV       : var        >-> val.
Coercion HnfV       : hnf        >-> val.
Coercion ValE       : val        >-> expr.
Coercion ExprEqn    : expr       >-> eqn.
Coercion int_to_hnf : Z          >-> hnf.
Coercion op_to_hnf  : primop     >-> hnf.

(** Notations matching the paper. *)
Declare Scope vc_scope.
Open Scope vc_scope.

Notation "e1 <|> e2"    := (ChoiceE e1 e2) (at level 50, left associativity) : vc_scope.
Notation "q ';' e"      := (SeqE q e)      (at level 60, right associativity) : vc_scope.
Notation "'EX' x , e"   := (ExE x e)       (at level 65, right associativity) : vc_scope.
Notation "v '=e' e"     := (EqEqn v e)     (at level 40)                     : vc_scope.
