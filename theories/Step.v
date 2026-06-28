(** * Single-step rewrite relation (Fig. 3)

    [step e e'] corresponds to one application of a rule from Fig. 3,
    at any subterm position (congruence rules at the bottom).

    Variable ordering for VAR-SWAP / SEQ-SWAP:
      [x < y] means atom [x] is bound MORE DEEPLY than [y] in the term,
      i.e., ∃y appears above ∃x in the scope chain.
      We represent this by the atom's natural order: deeper binding ↔
      larger atom (maintained by always picking fresh atoms with [pick_fresh]).
*)

Require Import VersRocq.Syntax.
Require Import VersRocq.Subst.
Require Import VersRocq.Contexts.
Require Import Metalib.Metatheory.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(** Atom ordering used in VAR-SWAP / SEQ-SWAP:
    [depth_lt x y] means x is bound strictly more deeply than y. *)
Notation depth_lt x y := (x > y)%nat.

Reserved Notation "e '-->' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=

  (* ==================== Application ==================== *)

  (** APP-ADD: add⟨k₁,k₂⟩ → k₃ *)
  | step_app_add : forall k1 k2,
      e_app (e_op op_add) (e_tuple [e_int k1; e_int k2])
      --> e_int (k1 + k2)%Z

  (** APP-GT: gt⟨k₁,k₂⟩ → k₁  if k₁ > k₂ *)
  | step_app_gt : forall k1 k2,
      (k2 < k1)%Z ->
      e_app (e_op op_gt) (e_tuple [e_int k1; e_int k2])
      --> e_int k1

  (** APP-GT-FAIL: gt⟨k₁,k₂⟩ → fail  if k₁ ≤ k₂ *)
  | step_app_gt_fail : forall k1 k2,
      (k1 <= k2)%Z ->
      e_app (e_op op_gt) (e_tuple [e_int k1; e_int k2])
      --> e_fail

  (** APP-BETA: (λx.e)(v) → ∃x. x=v; e
      Side condition: x ∉ fvs(v) guaranteed by Barendregt, made explicit. *)
  | step_app_beta : forall x e v,
      is_val v ->
      x `notin` fv v ->
      e_app (e_lam x e) v
      --> e_ex x (e_seq (e_eqn (e_var x) v) e)

  (** APP-TUP: ⟨v₀,…,vₙ⟩(v) → ∃x. x=v; (x=0; v₀ | … | x=n; vₙ)  x fresh
      (Narrowing: tuple application creates a choice over indices.) *)
  | step_app_tup : forall x vs v,
      vs <> [] ->
      is_val v ->
      x `notin` fv v ->
      x `notin` fold_right (fun e acc => fv e `union` acc) empty vs ->
      e_app (e_tuple vs) v
      --> e_ex x (e_seq (e_eqn (e_var x) v)
            (fold_right
               (fun '(i, vi) acc =>
                  e_choice (e_seq (e_eqn (e_var x) (e_int (Z.of_nat i))) vi) acc)
               e_fail
               (combine (seq 0 (length vs)) vs)))

  (** APP-TUP-0: ⟨⟩(v) → fail *)
  | step_app_tup_0 : forall v,
      is_val v ->
      e_app (e_tuple []) v --> e_fail

  (* ==================== Unification ==================== *)

  (** U-LIT: k=k; e → e *)
  | step_u_lit : forall k e,
      e_seq (e_eqn (e_int k) (e_int k)) e --> e

  (** U-TUP: ⟨v₁,…,vₙ⟩=⟨v₁',…,vₙ'⟩; e → v₁=v₁'; …; vₙ=vₙ'; e *)
  | step_u_tup : forall vs vs' e,
      length vs = length vs' ->
      e_seq (e_eqn (e_tuple vs) (e_tuple vs')) e
      --> fold_right (fun '(v, v') acc => e_seq (e_eqn v v') acc) e
                     (combine vs vs')

  (** U-FAIL: hnf₁=hnf₂; e → fail  (distinct non-lambda hnfs, or tuples of diff length) *)
  | step_u_fail : forall h1 h2 e,
      is_hnf h1 -> is_hnf h2 ->
      h1 <> h2 ->
      (forall x b, h1 <> e_lam x b) ->
      (forall x b, h2 <> e_lam x b) ->
      e_seq (e_eqn h1 h2) e --> e_fail

  (** U-OCCURS: x = V[x]; e → fail   (V ≠ □, i.e., x strictly inside a tuple) *)
  | step_u_occurs : forall x e rest,
      u_occurs_guard x e ->
      e_seq (e_eqn (e_var x) e) rest --> e_fail

  (** SUBST: X[x=v; e] → (X{v/x})[x=v; e{v/x}]   if v ≠ V[x] *)
  | step_subst : forall X x v e,
      is_val v ->
      ~ val_ctx_occ x v ->    (* v ≠ V[x]: x not at any value-context position in v *)
      fill_e X (e_seq (e_eqn (e_var x) v) e)
      --> fill_e (subst_ectx v x X) (e_seq (e_eqn (e_var x) v) (subst v x e))

  (** HNF-SWAP: hnf = v; e → v = hnf; e *)
  | step_hnf_swap : forall h v e,
      is_hnf h ->
      is_val v ->
      e_seq (e_eqn h v) e --> e_seq (e_eqn v h) e

  (** VAR-SWAP: y=x; e → x=y; e   if depth_lt x y  (x bound more deeply) *)
  | step_var_swap : forall x y e,
      depth_lt x y ->
      e_seq (e_eqn (e_var y) (e_var x)) e
      --> e_seq (e_eqn (e_var x) (e_var y)) e

  (** SEQ-SWAP: eq; x=v; e → x=v; eq; e
      unless eq is of the form y=v' with y ≤ x (to avoid infinite swap). *)
  | step_seq_swap : forall x v eq e,
      is_val v ->
      (forall y v', eq = e_eqn (e_var y) v' -> depth_lt x y) ->
      e_seq eq (e_seq (e_eqn (e_var x) v) e)
      --> e_seq (e_eqn (e_var x) v) (e_seq eq e)

  (* ==================== Elimination ==================== *)

  (** VAL-ELIM: v; e → e *)
  | step_val_elim : forall v e,
      is_val v ->
      e_seq v e --> e

  (** EXI-ELIM: ∃x. X[x=v; e] → X[e]
      if x ∉ fvs(X[e]) and v ≠ V[x]. *)
  | step_exi_elim : forall X x v e,
      is_val v ->
      x `notin` fv_ectx X ->
      x `notin` fv e ->
      ~ val_ctx_occ x v ->
      e_ex x (fill_e X (e_seq (e_eqn (e_var x) v) e))
      --> fill_e X e

  (** FAIL-ELIM: X[fail] → fail *)
  | step_fail_elim : forall X,
      X <> ec_hole ->
      fill_e X e_fail --> e_fail

  (* ==================== Normalization ==================== *)

  (** EXI-FLOAT: X[∃x. e] → ∃x. X[e]   if x ∉ fvs(X) *)
  | step_exi_float : forall X x e,
      x `notin` fv_ectx X ->
      fill_e X (e_ex x e) --> e_ex x (fill_e X e)

  (** SEQ-ASSOC: (eq; e₁); e₂ → eq; (e₁; e₂) *)
  | step_seq_assoc : forall eq e1 e2,
      e_seq (e_seq eq e1) e2 --> e_seq eq (e_seq e1 e2)

  (** EQN-FLOAT: v=(eq; e₁); e₂ → eq; (v=e₁; e₂) *)
  | step_eqn_float : forall v eq e1 e2,
      is_val v ->
      e_seq (e_eqn v (e_seq eq e1)) e2
      --> e_seq eq (e_seq (e_eqn v e1) e2)

  (** EXI-SWAP: ∃x. ∃y. e → ∃y. ∃x. e   (x ≠ y guaranteed by Barendregt) *)
  | step_exi_swap : forall x y e,
      x <> y ->
      e_ex x (e_ex y e) --> e_ex y (e_ex x e)

  (* ==================== Choice ==================== *)

  (** ONE-FAIL: one{fail} → fail *)
  | step_one_fail :
      e_one e_fail --> e_fail

  (** ONE-VALUE: one{v} → v *)
  | step_one_value : forall v,
      is_val v ->
      e_one v --> v

  (** ONE-CHOICE: one{v | e} → v *)
  | step_one_choice : forall v e,
      is_val v ->
      e_one (e_choice v e) --> v

  (** ALL-FAIL: all{fail} → ⟨⟩ *)
  | step_all_fail :
      e_all e_fail --> e_tuple []

  (** ALL-VALUE: all{v} → ⟨v⟩ *)
  | step_all_value : forall v,
      is_val v ->
      e_all v --> e_tuple [v]

  (** ALL-CHOICE: all{v₁ | … | vₙ} → ⟨v₁,…,vₙ⟩  (all branches are values) *)
  | step_all_choice : forall vs,
      vs <> [] ->
      Forall is_val vs ->
      e_all (fold_right e_choice e_fail vs) --> e_tuple vs

  (** CHOOSE-R: fail | e → e *)
  | step_choose_r : forall e,
      e_choice e_fail e --> e

  (** CHOOSE-L: e | fail → e *)
  | step_choose_l : forall e,
      e_choice e e_fail --> e

  (** CHOOSE-ASSOC: (e₁ | e₂) | e₃ → e₁ | (e₂ | e₃) *)
  | step_choose_assoc : forall e1 e2 e3,
      e_choice (e_choice e1 e2) e3 --> e_choice e1 (e_choice e2 e3)

  (** CHOOSE: SX[CX[e₁ | e₂]] → SX[CX[e₁] | CX[e₂]]
      Note: when CX contains ∃x binders, the two copies of CX share the name x.
      Under Barendregt, one copy must be alpha-renamed; this is noted as a TODO. *)
  | step_choose : forall SX CX e1 e2,
      fill_s SX (fill_c CX (e_choice e1 e2))
      --> fill_s SX (e_choice (fill_c CX e1) (fill_c CX e2))

  (* ==================== Congruence ==================== *)

  | step_lam    : forall x e e',    e --> e' -> e_lam x e --> e_lam x e'
  | step_ex     : forall x e e',    e --> e' -> e_ex  x e --> e_ex  x e'
  | step_app_l  : forall e1 e1' e2, e1 --> e1' -> e_app e1 e2 --> e_app e1' e2
  | step_app_r  : forall e1 e2 e2', e2 --> e2' -> e_app e1 e2 --> e_app e1 e2'
  | step_seq_l  : forall e1 e1' e2, e1 --> e1' -> e_seq e1 e2 --> e_seq e1' e2
  | step_seq_r  : forall e1 e2 e2', e2 --> e2' -> e_seq e1 e2 --> e_seq e1 e2'
  | step_eqn_l  : forall e1 e1' e2, e1 --> e1' -> e_eqn e1 e2 --> e_eqn e1' e2
  | step_eqn_r  : forall e1 e2 e2', e2 --> e2' -> e_eqn e1 e2 --> e_eqn e1 e2'
  | step_chl    : forall e1 e1' e2, e1 --> e1' -> e_choice e1 e2 --> e_choice e1' e2
  | step_chr    : forall e1 e2 e2', e2 --> e2' -> e_choice e1 e2 --> e_choice e1 e2'
  | step_one    : forall e e',      e --> e' -> e_one e --> e_one e'
  | step_all    : forall e e',      e --> e' -> e_all e --> e_all e'

where "e '-->' e'" := (step e e').

(* ================================================================= *)
(** ** Multi-step reduction *)

Inductive steps : expr -> expr -> Prop :=
  | steps_refl : forall e, steps e e
  | steps_step : forall e1 e2 e3,
      e1 --> e2 -> steps e2 e3 -> steps e1 e3.

Notation "e '-->*' e'" := (steps e e') (at level 40).

Lemma steps_trans : forall e1 e2 e3,
    e1 -->* e2 -> e2 -->* e3 -> e1 -->* e3.
Proof.
  intros e1 e2 e3 H12 H23.
  induction H12; auto.
  eapply steps_step; [exact H | apply IHsteps; exact H23].
Qed.

Lemma step_steps : forall e e',
    e --> e' -> e -->* e'.
Proof.
  intros. eapply steps_step; [exact H | apply steps_refl].
Qed.
