(** * Confluence (Theorem 4.1)

    The reduction relation [step] is confluent for well-behaved terms.

    Proof strategy (following Appendix C of the paper):
    1. Define [well_behaved e]: no obviously-problematic lambda-unification.
    2. Prove local confluence (WCR) by case analysis on pairs of redexes.
    3. Prove termination of the unification sub-system (VAR-SWAP / SEQ-SWAP /
       SUBST / HNF-SWAP) via a weight function on variable binding order.
    4. Apply Newman's lemma: WCR + SN of unification → CR for full system.
*)

Require Import VersRocq.Syntax.
Require Import VersRocq.Subst.
Require Import VersRocq.Contexts.
Require Import VersRocq.Step.
Require Import Metalib.Metatheory.

(* ================================================================= *)
(** ** Well-behaved terms (Section 4.1.3)

    A term is [well_behaved] if it never attempts to unify a lambda
    with another value, and contains no recursive (looping) structure
    that forces lambda-unification. *)

Definition obv_problematic_eqn (e : expr) : Prop :=
  (** An equation of the form [λx.b = v] or [v = λx.b] where v is not
      a variable (trying to unify a lambda with a known different value). *)
  exists x b v, is_val v -> (forall y b', v <> e_lam y b') ->
    e = e_eqn (e_lam x b) v \/ e = e_eqn v (e_lam x b).

Inductive well_behaved : expr -> Prop :=
  | wb_var    : forall x,         well_behaved (e_var x)
  | wb_int    : forall k,         well_behaved (e_int k)
  | wb_op     : forall o,         well_behaved (e_op o)
  | wb_fail   :                   well_behaved e_fail
  | wb_lam    : forall x e,       well_behaved e -> well_behaved (e_lam x e)
  | wb_ex     : forall x e,       well_behaved e -> well_behaved (e_ex x e)
  | wb_app    : forall e1 e2,     well_behaved e1 -> well_behaved e2 ->
                                  well_behaved (e_app e1 e2)
  | wb_seq    : forall e1 e2,
      well_behaved e1 -> well_behaved e2 ->
      ~ obv_problematic_eqn e1 ->
      well_behaved (e_seq e1 e2)
  | wb_eqn    : forall e1 e2,
      well_behaved e1 -> well_behaved e2 ->
      ~ obv_problematic_eqn (e_eqn e1 e2) ->
      well_behaved (e_eqn e1 e2)
  | wb_choice : forall e1 e2,     well_behaved e1 -> well_behaved e2 ->
                                  well_behaved (e_choice e1 e2)
  | wb_one    : forall e,         well_behaved e -> well_behaved (e_one e)
  | wb_all    : forall e,         well_behaved e -> well_behaved (e_all e)
  | wb_tuple  : forall vs,        Forall well_behaved vs ->
                                  well_behaved (e_tuple vs).

(* ================================================================= *)
(** ** Confluence *)

Definition confluent_at (e : expr) : Prop :=
  forall e1 e2,
    e -->* e1 -> e -->* e2 ->
    exists e', e1 -->* e' /\ e2 -->* e'.

(** Theorem 4.1 (Confluence): [step] is confluent for well-behaved terms. *)
Theorem confluence : forall e,
    well_behaved e ->
    confluent_at e.
Proof.
  (* TODO: follow Appendix C proof structure *)
Admitted.
