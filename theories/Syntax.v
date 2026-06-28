(** * Syntax of the Verse Calculus (Fig. 1)

    Named-variable representation with the Barendregt convention.
    Variables are Metalib [atom]s (= positive integers).
    Binders: [e_lam x e] for λx.e, [e_ex x e] for ∃x.e.
    Well-scoping invariant [ws S e] (Barendregt): every binder in [e]
    introduces a name fresh from [S] and from all other binders in [e].
    Top-level: [wf e  :=  ws (fv e) e].
*)

Require Import Metalib.Metatheory.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* ================================================================= *)
(** ** Primitive operators *)

Inductive primop : Type := op_gt | op_add.

(* ================================================================= *)
(** ** Expressions

    e  ::= v | eq; e | ∃x. e | fail | e₁ | e₂ | v₁ v₂ | one{e} | all{e}
    eq ::= e | v = e
    v  ::= x | hnf
    hnf ::= k | op | ⟨v₁,…,vₙ⟩ | λx. e
*)

Inductive expr : Type :=
  | e_var    : atom   -> expr                  (* x              *)
  | e_int    : Z      -> expr                  (* k              *)
  | e_op     : primop -> expr                  (* gt | add       *)
  | e_lam    : atom   -> expr -> expr          (* λx. e  binder  *)
  | e_ex     : atom   -> expr -> expr          (* ∃x. e  binder  *)
  | e_app    : expr   -> expr -> expr          (* v₁ v₂          *)
  | e_seq    : expr   -> expr -> expr          (* e₁; e₂         *)
  | e_eqn    : expr   -> expr -> expr          (* v = e          *)
  | e_fail   : expr                            (* fail           *)
  | e_choice : expr   -> expr -> expr          (* e₁ | e₂        *)
  | e_one    : expr   -> expr                  (* one{e}         *)
  | e_all    : expr   -> expr                  (* all{e}         *)
  | e_tuple  : list expr -> expr.              (* ⟨v₁,…,vₙ⟩      *)

(* ================================================================= *)
(** ** Free and bound variables *)

Fixpoint fv (e : expr) : atoms :=
  match e with
  | e_var x        => singleton x
  | e_int _        => empty
  | e_op  _        => empty
  | e_lam x body   => remove x (fv body)
  | e_ex  x body   => remove x (fv body)
  | e_app e1 e2    => fv e1 `union` fv e2
  | e_seq e1 e2    => fv e1 `union` fv e2
  | e_eqn e1 e2    => fv e1 `union` fv e2
  | e_fail         => empty
  | e_choice e1 e2 => fv e1 `union` fv e2
  | e_one e        => fv e
  | e_all e        => fv e
  | e_tuple vs     => fold_right (fun e' acc => fv e' `union` acc) empty vs
  end.

Fixpoint bv (e : expr) : atoms :=
  match e with
  | e_lam x body   => singleton x `union` bv body
  | e_ex  x body   => singleton x `union` bv body
  | e_app e1 e2    => bv e1 `union` bv e2
  | e_seq e1 e2    => bv e1 `union` bv e2
  | e_eqn e1 e2    => bv e1 `union` bv e2
  | e_choice e1 e2 => bv e1 `union` bv e2
  | e_one e        => bv e
  | e_all e        => bv e
  | e_tuple vs     => fold_right (fun e' acc => bv e' `union` acc) empty vs
  | _              => empty
  end.

(* ================================================================= *)
(** ** Barendregt well-scoping

    [ws S e]: every binder in [e] introduces a name fresh from [S]
    and from all other binders encountered so far.
    [S] accumulates both the "outer free variables" and previously seen
    bound names, ensuring all binders are globally distinct.
*)

Inductive ws : atoms -> expr -> Prop :=
  | ws_var    : forall S x,         ws S (e_var x)
  | ws_int    : forall S k,         ws S (e_int k)
  | ws_op     : forall S o,         ws S (e_op o)
  | ws_fail   : forall S,           ws S e_fail
  | ws_lam    : forall S x body,
      x `notin` S ->
      ws (S `union` singleton x) body ->
      ws S (e_lam x body)
  | ws_ex     : forall S x body,
      x `notin` S ->
      ws (S `union` singleton x) body ->
      ws S (e_ex x body)
  | ws_app    : forall S e1 e2,     ws S e1 -> ws S e2 -> ws S (e_app e1 e2)
  | ws_seq    : forall S e1 e2,     ws S e1 -> ws S e2 -> ws S (e_seq e1 e2)
  | ws_eqn    : forall S e1 e2,     ws S e1 -> ws S e2 -> ws S (e_eqn e1 e2)
  | ws_choice : forall S e1 e2,     ws S e1 -> ws S e2 -> ws S (e_choice e1 e2)
  | ws_one    : forall S e,         ws S e  -> ws S (e_one e)
  | ws_all    : forall S e,         ws S e  -> ws S (e_all e)
  | ws_tuple  : forall S vs,        Forall (ws S) vs -> ws S (e_tuple vs).

(** Full Barendregt condition: binders fresh from free variables and each other. *)
Definition wf (e : expr) : Prop := ws (fv e) e.

(** Monotonicity: well-scoping is preserved by enlarging S. *)
Lemma ws_weaken : forall S T e,
    ws S e -> S [<=] T -> ws T e.
Proof.
  intros S T e H. revert T.
  induction H; intros T Hsub; constructor; auto.
  - apply IHws. fsetdec.
  - apply IHws. fsetdec.
  - apply IHws. fsetdec.
  - apply IHws. fsetdec.
  - eapply Forall_impl; [| exact H].
    intros e' He'. apply He'. exact Hsub.
Qed.

(* ================================================================= *)
(** ** Head-normal forms and values *)

(** hnf ::= k | op | ⟨v₁,…,vₙ⟩ | λx. e *)
Inductive is_hnf : expr -> Prop :=
  | hnf_int   : forall k,   is_hnf (e_int k)
  | hnf_op    : forall o,   is_hnf (e_op o)
  | hnf_tuple : forall vs,  is_hnf (e_tuple vs)
  | hnf_lam   : forall x e, is_hnf (e_lam x e).

(** v ::= x | hnf *)
Inductive is_val : expr -> Prop :=
  | val_var : forall x,  is_val (e_var x)
  | val_hnf : forall e,  is_hnf e -> is_val e.

Lemma is_val_hnf : forall e, is_hnf e -> is_val e.
Proof. intros. apply val_hnf. exact H. Qed.

(** hnf is never a variable. *)
Lemma hnf_not_var : forall x, ~ is_hnf (e_var x).
Proof. intros x H. inversion H. Qed.
