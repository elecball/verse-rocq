(** * Context types (Fig. 4)

    Execution context  X  ::= □ | v=X; e | X; e | eq; X
    Value context      V  ::= □ | ⟨vs, [·], vs'⟩
    Choice context     CX ::= □ | v=CX; e | CX; e | ceq; CX | ∃x. CX
    Scope context      SX ::= one{SC} | all{SC}
                       SC ::= □ | SC | e | e | SC

    Each context is an inductive data type; [fill_*] fills the hole.
    [subst_ectx] / [subst_cctx] lift substitution to contexts.
    [val_ctx_occ x e] expresses "x occurs in e at a value-context position"
    (used in U-OCCURS and the SUBST guard).
*)

Require Import VersRocq.Syntax.
Require Import VersRocq.Subst.
Require Import Metalib.Metatheory.
Require Import Coq.Lists.List.
Import ListNotations.

(* ================================================================= *)
(** ** Execution context  X *)

Inductive ectx : Type :=
  | ec_hole      : ectx
  | ec_eqn_rhs   : expr -> ectx -> expr -> ectx   (** v = [X]; e  *)
  | ec_seq_left  : ectx -> expr -> ectx             (** [X]; e      *)
  | ec_seq_right : expr -> ectx -> ectx.            (** eq; [X]     *)

Fixpoint fill_e (X : ectx) (e : expr) : expr :=
  match X with
  | ec_hole             => e
  | ec_eqn_rhs v X' r  => e_seq (e_eqn v (fill_e X' e)) r
  | ec_seq_left X' e2   => e_seq (fill_e X' e) e2
  | ec_seq_right eq X'  => e_seq eq (fill_e X' e)
  end.

Fixpoint fv_ectx (X : ectx) : atoms :=
  match X with
  | ec_hole             => empty
  | ec_eqn_rhs v X' r  => fv v `union` fv_ectx X' `union` fv r
  | ec_seq_left X' e2   => fv_ectx X' `union` fv e2
  | ec_seq_right eq X'  => fv eq `union` fv_ectx X'
  end.

Fixpoint subst_ectx (u : expr) (x : atom) (X : ectx) : ectx :=
  match X with
  | ec_hole             => ec_hole
  | ec_eqn_rhs v X' r  =>
      ec_eqn_rhs (subst u x v) (subst_ectx u x X') (subst u x r)
  | ec_seq_left X' e2   => ec_seq_left (subst_ectx u x X') (subst u x e2)
  | ec_seq_right eq X'  => ec_seq_right (subst u x eq) (subst_ectx u x X')
  end.

(** Key identity: fill commutes with substitution. *)
Lemma fill_e_subst : forall X u x e,
    subst u x (fill_e X e) = fill_e (subst_ectx u x X) (subst u x e).
Proof.
  induction X; intros; simpl; auto.
  - rewrite IHX. reflexivity.
  - rewrite IHX. reflexivity.
  - rewrite IHX. reflexivity.
Qed.

(* ================================================================= *)
(** ** Value context  V *)

(** V ::= □ | ⟨ls, [·], rs⟩  where ls and rs are value lists. *)
Inductive vctx : Type :=
  | vc_hole  : vctx
  | vc_tuple : list expr -> vctx -> list expr -> vctx.

Fixpoint fill_v (V : vctx) (e : expr) : expr :=
  match V with
  | vc_hole         => e
  | vc_tuple ls V' rs => e_tuple (ls ++ [fill_v V' e] ++ rs)
  end.

(** [val_ctx_occ x e]: x occurs at a value-context position in e.
    Equivalently, ∃ V, fill_v V (e_var x) = e. *)
Definition val_ctx_occ (x : atom) (e : expr) : Prop :=
  exists V, fill_v V (e_var x) = e.

(** The U-OCCURS guard: x occurs STRICTLY inside a value structure (V ≠ □). *)
Definition u_occurs_guard (x : atom) (e : expr) : Prop :=
  val_ctx_occ x e /\ e <> e_var x.

(* ================================================================= *)
(** ** Choice context  CX *)

(** CX ::= □ | v=CX; e | CX; e | ceq; CX | ∃x. CX
    Unlike X, CX may cross ∃ binders (but not λ). *)
Inductive cctx : Type :=
  | cc_hole      : cctx
  | cc_eqn_rhs   : expr -> cctx -> expr -> cctx
  | cc_seq_left  : cctx -> expr -> cctx
  | cc_seq_right : expr -> cctx -> cctx
  | cc_ex        : atom -> cctx -> cctx.            (** ∃x. [CX]   *)

Fixpoint fill_c (CX : cctx) (e : expr) : expr :=
  match CX with
  | cc_hole             => e
  | cc_eqn_rhs v CX' r => e_seq (e_eqn v (fill_c CX' e)) r
  | cc_seq_left CX' e2  => e_seq (fill_c CX' e) e2
  | cc_seq_right eq CX' => e_seq eq (fill_c CX' e)
  | cc_ex x CX'         => e_ex x (fill_c CX' e)
  end.

Fixpoint subst_cctx (u : expr) (x : atom) (CX : cctx) : cctx :=
  match CX with
  | cc_hole             => cc_hole
  | cc_eqn_rhs v CX' r =>
      cc_eqn_rhs (subst u x v) (subst_cctx u x CX') (subst u x r)
  | cc_seq_left CX' e2  => cc_seq_left (subst_cctx u x CX') (subst u x e2)
  | cc_seq_right eq CX' => cc_seq_right (subst u x eq) (subst_cctx u x CX')
  | cc_ex y CX'         => cc_ex y (subst_cctx u x CX')
  end.

Lemma fill_c_subst : forall CX u x e,
    subst u x (fill_c CX e) = fill_c (subst_cctx u x CX) (subst u x e).
Proof.
  induction CX; intros; simpl; auto.
  - rewrite IHCX. reflexivity.
  - rewrite IHCX. reflexivity.
  - rewrite IHCX. reflexivity.
  - rewrite IHCX. reflexivity.
Qed.

(** Bound variables introduced by a choice context. *)
Fixpoint bv_cctx (CX : cctx) : atoms :=
  match CX with
  | cc_hole             => empty
  | cc_eqn_rhs _ CX' _ => bv_cctx CX'
  | cc_seq_left CX' _   => bv_cctx CX'
  | cc_seq_right _ CX'  => bv_cctx CX'
  | cc_ex x CX'         => singleton x `union` bv_cctx CX'
  end.

(* ================================================================= *)
(** ** Scope context  SX / SC *)

(** SC ::= □ | SC | e | e | SC  (binary choice tree with a single hole) *)
Inductive sccnt : Type :=
  | sc_hole  : sccnt
  | sc_left  : sccnt -> expr -> sccnt   (** [SC] | e   *)
  | sc_right : expr -> sccnt -> sccnt.  (** e | [SC]   *)

Fixpoint fill_sc (SC : sccnt) (e : expr) : expr :=
  match SC with
  | sc_hole        => e
  | sc_left SC' r  => e_choice (fill_sc SC' e) r
  | sc_right l SC' => e_choice l (fill_sc SC' e)
  end.

(** SX ::= one{SC} | all{SC} *)
Inductive sctx : Type :=
  | sx_one : sccnt -> sctx
  | sx_all : sccnt -> sctx.

Definition fill_s (SX : sctx) (e : expr) : expr :=
  match SX with
  | sx_one SC => e_one (fill_sc SC e)
  | sx_all SC => e_all (fill_sc SC e)
  end.
