(** * Capture-avoiding substitution

    Under the Barendregt convention, all binders are already fresh,
    so [subst u x e] needs no renaming.  The key lemma [ws_subst]
    shows the convention is preserved by substitution.
*)

Require Import VersRocq.Syntax.
Require Import Metalib.Metatheory.
Require Import Coq.Lists.List.
Import ListNotations.

(* ================================================================= *)
(** ** Substitution  [u / x] e *)

Fixpoint subst (u : expr) (x : atom) (e : expr) : expr :=
  match e with
  | e_var y        => if x == y then u else e_var y
  | e_lam y body   => e_lam y (subst u x body)
  | e_ex  y body   => e_ex  y (subst u x body)
  | e_app e1 e2    => e_app  (subst u x e1) (subst u x e2)
  | e_seq e1 e2    => e_seq  (subst u x e1) (subst u x e2)
  | e_eqn e1 e2    => e_eqn  (subst u x e1) (subst u x e2)
  | e_choice e1 e2 => e_choice (subst u x e1) (subst u x e2)
  | e_one e        => e_one  (subst u x e)
  | e_all e        => e_all  (subst u x e)
  | e_tuple vs     => e_tuple (map (subst u x) vs)
  | e_int _        => e
  | e_op  _        => e
  | e_fail         => e
  end.

Notation "[ u / x ] e" := (subst u x e) (at level 67).

(* ================================================================= *)
(** ** Basic properties *)

Lemma subst_fresh : forall x e u,
    x `notin` fv e ->
    [u / x] e = e.
Proof.
  intros x e. induction e; intros u Hfr; simpl in *; auto.
  - destruct (x == a).
    + subst. exfalso. apply Hfr. fsetdec.
    + reflexivity.
  - f_equal. apply IHe. fsetdec.
  - f_equal. apply IHe. fsetdec.
  - f_equal; [apply IHe1 | apply IHe2]; fsetdec.
  - f_equal; [apply IHe1 | apply IHe2]; fsetdec.
  - f_equal; [apply IHe1 | apply IHe2]; fsetdec.
  - f_equal; [apply IHe1 | apply IHe2]; fsetdec.
  - f_equal. apply IHe. fsetdec.
  - f_equal. apply IHe. fsetdec.
  - f_equal. induction l; simpl in *; auto.
    f_equal.
    + apply H; [left; reflexivity | fsetdec].
    + apply IHl.
      * intros e' Hin Hfr'. apply H; [right; exact Hin | exact Hfr'].
      * fsetdec.
Qed.

Lemma fv_subst : forall e u x,
    fv ([u / x] e) [<=] fv u `union` remove x (fv e).
Proof.
  induction e; intros u x; simpl; try fsetdec.
  - destruct (x == a); simpl; fsetdec.
  - specialize (IHe u x). fsetdec.
  - specialize (IHe u x). fsetdec.
  - specialize (IHe1 u x). specialize (IHe2 u x). fsetdec.
  - specialize (IHe1 u x). specialize (IHe2 u x). fsetdec.
  - specialize (IHe1 u x). specialize (IHe2 u x). fsetdec.
  - specialize (IHe1 u x). specialize (IHe2 u x). fsetdec.
  - specialize (IHe u x). fsetdec.
  - specialize (IHe u x). fsetdec.
  - induction l; simpl; [fsetdec |].
    assert (fv ([u / x] a) [<=] fv u `union` remove x (fv a))
      by (apply H; left; reflexivity).
    assert (fv (e_tuple (map (subst u x) l)) [<=] fv u `union` remove x (fold_right (fun e' acc => fv e' `union` acc) empty l)).
    { simpl. apply IHl. intros e' Hin. apply H. right. exact Hin. }
    simpl in H1. fsetdec.
Qed.

(** Under Barendregt, substitution preserves well-scoping. *)
Lemma ws_subst : forall S e u x,
    ws S e ->
    ws S u ->
    x `notin` bv e ->        (* Barendregt: binders in e don't shadow x *)
    ws S ([u / x] e).
Proof.
  intros S e u x Hws. revert u.
  induction Hws; intros u Hwsu Hnobv; simpl; try constructor; auto.
  - destruct (x0 == x); subst; [exact Hwsu | constructor].
  - apply IHHws; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws1; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws2; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws1; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws2; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws1; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws2; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws1; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws2; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - apply IHHws; [exact Hwsu |]. simpl in Hnobv. fsetdec.
  - constructor.
    induction H; simpl in *; constructor.
    + apply H0; [exact Hwsu | fsetdec].
    + apply IHForall; intros; fsetdec.
Qed.
