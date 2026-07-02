From Stdlib Require Import ZArith List PeanoNat Lia Wf_nat.
Import ListNotations.
From VersRocq Require Import Syntax Context Rewrite.
Open Scope Z_scope.
Open Scope vc_scope.


(*******************************************)
(* B.1 :  Reduction relations              *)
(*******************************************)

(* B.1  Binary Relations *)
Definition binary_relation (A : Type) : Type := A -> A -> Prop.


(* B.3  Reduction Relations *)
Definition compatible (R : binary_relation expr) : Prop :=
  forall (X : xctx) (m n : expr), R m n -> R (xfill X m) (xfill X n).

Definition is_reduction (R : binary_relation expr) : Prop := compatible R.


(* B.4  Derived Relations *)
Fixpoint rel_pow {A : Type} (R : binary_relation A) (k : nat) : A -> A -> Prop :=
  match k with
  | 0%nat => fun e1 e2 => e1 = e2
  | S k'  => fun e1 e2 => exists e3, R e1 e3 /\ rel_pow R k' e3 e2
  end.

Definition rel_star {A : Type} (R : binary_relation A) : A -> A -> Prop :=
  fun e1 e2 => exists k, rel_pow R k e1 e2.

Definition steps {A : Type} (R : binary_relation A) : A -> A -> Prop :=
  fun e1 e2 => R e1 e2.

Definition skips {A : Type} (R : binary_relation A) : A -> A -> Prop :=
  fun e1 e2 => e1 = e2 \/ R e1 e2.

Definition reduces {A : Type} (R : binary_relation A) : A -> A -> Prop :=
  fun e1 e2 => rel_star R e1 e2.

Definition steps_k {A : Type} (R : binary_relation A) (k : nat) : A -> A -> Prop :=
  fun e1 e2 => rel_pow R k e1 e2.

Notation "a =[ R ]=>  b"        := (steps R a b)     (at level 50, R at level 99).
Notation "a =[ R ]=>?  b"       := (skips R a b)     (at level 50, R at level 99).
Notation "a =[ R ]=>>  b"       := (reduces R a b)   (at level 50, R at level 99).
Notation "a =[ R | k ]=>>  b"   := (steps_k R k a b) (at level 50, R at level 99, k at level 0).

Definition rel_union {A} (R S : binary_relation A) : binary_relation A :=
  fun a b => R a b \/ S a b.

Notation "R \u/ S" := (rel_union R S) (at level 45).

Definition rel_comp {A} (X Y : binary_relation A) : binary_relation A :=
  fun a b => exists c, X a c /\ Y c b.

Notation "R ;; S" := (rel_comp R S) (at level 45).

Lemma steps_to_skips {A} (R : binary_relation A) : forall e1 e2,
  e1 =[R]=> e2 -> e1 =[R]=>? e2.
Proof.
  intros e1 e2 H.
  right; exact H.
Qed.

Lemma steps_to_steps_1 {A} (R : binary_relation A) : forall e1 e2,
  e1 =[R]=> e2 -> e1 =[R|1]=>> e2.
Proof.
  intros e1 e2 H. unfold steps_k, rel_pow. exists e2. split; auto.
Qed.

Lemma steps_k_to_reduces {A} (R : binary_relation A) : forall k a b,
  a =[R|k]=>> b -> a =[R]=>> b.
Proof.
  intros k a b H. unfold reduces, rel_star. exists k. exact H.
Qed.

Lemma steps_to_reduces {A} (R : binary_relation A) : forall a b,
  a =[R]=> b -> a =[R]=>> b.
Proof.
  intros a b H. apply (steps_k_to_reduces R 1).
  unfold steps_k, rel_pow. exists b. split; auto.
Qed.

Lemma skips_to_reduces {A} (R : binary_relation A) : forall a b,
  a =[R]=>? b -> a =[R]=>> b.
Proof.
  intros a b [Heq | Hstep].
  - subst. unfold reduces, rel_star. exists 0%nat. reflexivity.
  - apply steps_to_reduces. exact Hstep.
Qed.

Lemma skips_refl {A} (R : binary_relation A) : forall a, a =[R]=>? a.
Proof.
  intro a. left. reflexivity.
Qed.

Lemma reduces_refl {A} (R : binary_relation A) : forall a, a =[R]=>> a.
Proof.
  intro a. unfold reduces, rel_star. exists 0%nat. reflexivity.
Qed.

Lemma steps_k_trans {A} (R : binary_relation A) : forall k1 k2 a b c,
  steps_k R k1 a b -> steps_k R k2 b c -> steps_k R (k1 + k2)%nat a c.
Proof.
  induction k1 as [| k1 IH].
  - intros k2 a b c H1 H2. simpl in H1. subst. simpl. exact H2.
  - intros k2 a b c H1 H2.
    unfold steps_k in *. simpl in H1 |- *.
    destruct H1 as [e [HRae H1]].
    exists e. split. exact HRae. apply (IH k2 e b c H1 H2).
Qed.

Lemma reduces_trans {A} (R : binary_relation A) : forall a b c,
  a =[R]=>> b -> b =[R]=>> c -> a =[R]=>> c.
Proof.
  intros a b c [k1 H1] [k2 H2].
  unfold reduces, rel_star. exists (k1 + k2)%nat.
  exact (steps_k_trans R k1 k2 a b c H1 H2).
Qed.

Lemma steps_k_split {A} (R : binary_relation A) : forall k1 k2 a b,
  steps_k R (k1 + k2)%nat a b -> exists c, steps_k R k1 a c /\ steps_k R k2 c b.
Proof.
  induction k1 as [| k1 IH].
  - intros k2 a b H. simpl in H. exists a. split; [reflexivity | exact H].
  - intros k2 a b H. simpl in H. destruct H as [a1 [HRaa1 H]].
    destruct (IH k2 a1 b H) as [c [Hc1 Hc2]].
    exists c. split.
    + simpl. exists a1. split; [exact HRaa1 | exact Hc1].
    + exact Hc2.
Qed.


(* B.5  Reduction Size *)
Definition reduction_size {A} (R : binary_relation A) (a b : A) (result : option nat) : Prop :=
  match result with
  | None   => ~ (a =[R]=>> b)
  | Some k => a =[R|k]=>> b /\ forall k', (k' < k)%nat -> ~ a =[R|k']=>> b
  end.

Lemma reduction_size_unique {A} (R : binary_relation A) (a b : A) (r1 r2 : option nat) :
  reduction_size R a b r1 -> reduction_size R a b r2 -> r1 = r2.
Proof.
  intros H1 H2.
  destruct r1 as [k1|], r2 as [k2|]; simpl in *.
  - destruct H1 as [Hk1 Hmin1], H2 as [Hk2 Hmin2].
    f_equal.
    destruct (Nat.lt_trichotomy k1 k2) as [Hlt | [Heq | Hgt]].
    + exfalso. apply (Hmin2 k1 Hlt). exact Hk1.
    + exact Heq.
    + exfalso. apply (Hmin1 k2 Hgt). exact Hk2.
  - exfalso. destruct H1 as [Hk1 _]. apply H2.
    unfold reduces, rel_star. exists k1. exact Hk1.
  - exfalso. destruct H2 as [Hk2 _]. apply H1.
    unfold reduces, rel_star. exists k2. exact Hk2.
  - reflexivity.
Qed.


(* Definition B.6: Normal Forms *)
Definition is_nf {A} (R : binary_relation A) (a : A) : Prop :=
  forall b, ~ a =[R]=> b.

(*******************************************)
(* B.2 :  Confluence                       *)
(*******************************************)

(* Definition B.7: Diamond Property *)
Definition diamond_property {A} (R : binary_relation A) : Prop :=
  forall a b c, a =[R]=> b -> a =[R]=> c ->
    exists d, b =[R]=> d /\ c =[R]=> d.

(* Definition B.8: Confluence *)
Definition confluent {A} (R : binary_relation A) : Prop :=
  forall a b c, a =[R]=>> b -> a =[R]=>> c ->
    exists d, b =[R]=>> d /\ c =[R]=>> d.

(* Definition B.9: Local Confluence *)
Definition locally_confluent {A} (R : binary_relation A) : Prop :=
  forall a b c, a =[R]=> b -> a =[R]=> c ->
    exists d, b =[R]=>> d /\ c =[R]=>> d.

(* Lemma B.10: Diamond property implies confluence *)
Lemma diamond_strip {A} (R : binary_relation A) : diamond_property R ->
  forall n a b c, a =[R]=> b -> steps_k R n a c ->
    exists d, b =[R]=>> d /\ c =[R]=>> d.
Proof.
  intros H_diamond n.
  induction n as [| n IH].
  - intros a b c HRab H0. unfold steps_k in H0. simpl in H0. subst.
    exists b. split. apply reduces_refl. apply steps_to_reduces. exact HRab.
  - intros a b c HRab H.
    unfold steps_k in H. simpl in H. destruct H as [a' [HRaa' H]].
    destruct (H_diamond a b a' HRab HRaa') as [g [HRbg HRa'g]].
    destruct (IH a' g c HRa'g H) as [d [Hgd Hcd]].
    exists d. split.
    + apply reduces_trans with g.
      * apply steps_to_reduces. exact HRbg.
      * exact Hgd.
    + exact Hcd.
Qed.
Abbreviation LB10 := diamond_strip.

Lemma diamond_implies_confluent {A} (R : binary_relation A) :
  diamond_property R -> confluent R.
Proof.
  intro H_diamond.
  intros a b c [kb Hab] Hac.
  revert a b c Hab Hac.
  induction kb as [| kb IH].
  - intros a b c Hab Hac. simpl in Hab. subst.
    exists c. split. exact Hac. apply reduces_refl.
  - intros a b c Hab Hac.
    simpl in Hab. destruct Hab as [a' [HRaa' Hkb_a'b]].
    destruct Hac as [kc Hkc_ac].
    destruct (LB10 R H_diamond kc a a' c HRaa' Hkc_ac) as [g [Ha'g Hcg]].
    destruct (IH a' b g Hkb_a'b Ha'g) as [d [Hbd Hgd]].
    exists d. split.
    + exact Hbd.
    + exact (reduces_trans R c g d Hcg Hgd).
Qed.

(* Lemma B.11: Unicity - confluent implies unique normal forms *)
Lemma unicity {A} (R : binary_relation A) : confluent R ->
  forall a b c, a =[R]=>> b -> is_nf R b -> a =[R]=>> c -> is_nf R c -> b = c.
Proof.
  intros H_conf a b c Hab Hnfb Hac Hnfc.
  destruct (H_conf a b c Hab Hac) as [d [[kb Hbd] [kc Hcd]]].
  unfold is_nf in *.
  destruct kb.
  - simpl in Hbd. subst.
    destruct kc.
    + simpl in Hcd. subst. reflexivity.
    + simpl in Hcd. destruct Hcd as [e [HRde _]].
      exfalso. apply (Hnfc e). exact HRde.
  - simpl in Hbd. destruct Hbd as [e [HRbe _]].
    exfalso. apply (Hnfb e). exact HRbe.
Qed.
Abbreviation LB11 := unicity.

(* Lemma B.12: Closure - confluent implies R* is confluent *)
Lemma closure {A} (R : binary_relation A) : confluent R -> confluent (rel_star R).
Proof.
  unfold confluent. 
  assert (forall a b, a =[ (rel_star R) ]=>> b -> a =[ R ]=>> b).
  - unfold reduces, rel_star. intros.
    destruct H as [k ?].
    revert k a b H.
    induction k.
    + intros. inversion H. subst.
      exists 0%nat. constructor.
    + intros. destruct H as [c [[k1 H1] H2]].
      apply IHk in H2.
      destruct H2 as [k2 ?].
      assert (H3 := steps_k_trans R k1 k2 a c b H1 H).
      exists (k1 + k2)%nat.
      auto. 
  - assert (forall a b, a =[ R ]=>> b -> a =[ (rel_star R) ]=>> b).
    + unfold reduces, rel_star. intros.
      destruct H0 as [k ?].
      exists 1%nat. simpl.
      exists b. constructor; auto.
      exists k. auto. 
    + intros. apply H in H2, H3.
      pose proof (H1 a b c H2 H3).
      destruct H4 as [d [? ?]].
      apply H0 in H4, H5.
      exists d. eauto.
Qed.
Abbreviation LB12 := closure.

(* Definition B.13: Noetherian *)
Definition noetherian {A} (R : binary_relation A) : Prop :=
  forall e, Acc (fun b a => a =[R]=> b) e.

(* Lemma B.14: Newman's Lemma *)
Lemma newman_aux {A} (R : binary_relation A) : locally_confluent R ->
  forall e, Acc (fun b a => a =[R]=> b) e ->
  forall e1 e2, e =[R]=>> e1 -> e =[R]=>> e2 ->
    exists d, e1 =[R]=>> d /\ e2 =[R]=>> d.
Proof.
  intros H_local e Hacc.
  induction Hacc as [e _ IHe].
  intros e1 e2 [k1 H1] [k2 H2].
  destruct k1 as [| k1'].
  - simpl in H1. subst.
    exists e2. split. unfold reduces, rel_star. exists k2. exact H2. apply reduces_refl.
  - simpl in H1. destruct H1 as [e3 [HRe_e3 H1']].
    destruct k2 as [| k2'].
    + simpl in H2. subst.
      exists e1. split. apply reduces_refl.
      unfold reduces, rel_star. exists (S k1'). simpl. exists e3. split; assumption.
    + simpl in H2. destruct H2 as [e4 [HRe_e4 H2']].
      destruct (H_local e e3 e4 HRe_e3 HRe_e4) as [c [Hc1 Hc2]].
      assert (He3_e1 : e3 =[R]=>> e1) by (apply (steps_k_to_reduces R k1'); exact H1').
      assert (He4_e2 : e4 =[R]=>> e2) by (apply (steps_k_to_reduces R k2'); exact H2').
      destruct (IHe e3 HRe_e3 e1 c He3_e1 Hc1) as [d1 [Hd11 Hd12]].
      destruct (IHe e4 HRe_e4 e2 c He4_e2 Hc2) as [d2 [Hd21 Hd22]].
      destruct (IHe e3 HRe_e3 d1 d2
        (reduces_trans R e3 c d1 Hc1 Hd12)
        (reduces_trans R e3 c d2 Hc1 Hd22)) as [d3 [Hd13 Hd23]].
      exists d3. split.
      * exact (reduces_trans R e1 d1 d3 Hd11 Hd13).
      * exact (reduces_trans R e2 d2 d3 Hd21 Hd23).
Qed.
Abbreviation LB14 := newman_aux.

Lemma newman {A} (R : binary_relation A) : locally_confluent R -> noetherian R -> confluent R.
Proof.
  intros H_local H_noeth e1 e2 e3 H12 H13.
  exact (LB14 R H_local e1 (H_noeth e1) e2 e3 H12 H13).
Qed.

(* Definition B.15: Strong Confluence *)
Definition strongly_confluent {A} (R : binary_relation A) : Prop :=
  forall a b c, a =[R]=> b -> a =[R]=> c ->
    b =[R]=>? c \/ exists d, b =[R]=>> d /\ c =[R]=> d.

(* Lemma B.16: Strong confluence implies confluence *)
Lemma strong_strip {A} (R : binary_relation A) : strongly_confluent R ->
  forall n a b c, a =[R]=> b -> steps_k R n a c ->
    exists d, b =[R]=>> d /\ c =[R]=>> d.
Proof.
  intros H_strong n.
  induction n as [| n IH].
  - intros a b c HRab H0. simpl in H0. subst.
    exists b. split. apply reduces_refl. apply steps_to_reduces. exact HRab.
  - intros a b c HRab H.
    simpl in H. destruct H as [a' [HRaa' H]].
    destruct (H_strong a b a' HRab HRaa') as [[Heq | HRba'] | [g [Hbg HRa'g]]].
    + rewrite <- Heq in H.
      exists c. split.
      * exact (steps_k_to_reduces R n b c H).
      * apply reduces_refl.
    + exists c. split.
      * exact (reduces_trans R b a' c
          (steps_to_reduces R b a' HRba')
          (steps_k_to_reduces R n a' c H)).
      * apply reduces_refl.
    + destruct (IH a' g c HRa'g H) as [d [Hgd Hcd]].
      exists d. split.
      * exact (reduces_trans R b g d Hbg Hgd).
      * exact Hcd.
Qed.
Abbreviation LB16 := strong_strip.

Lemma strongly_confluent_implies_confluent {A} (R : binary_relation A) :
  strongly_confluent R -> confluent R.
Proof.
  intro H_strong.
  intros a b c [kb Hab] Hac.
  revert a b c Hab Hac.
  induction kb as [| kb IH].
  - intros a b c Hab Hac. simpl in Hab. subst.
    exists c. split. exact Hac. apply reduces_refl.
  - intros a b c Hab Hac.
    simpl in Hab. destruct Hab as [a' [HRaa' Hkb_a'b]].
    destruct Hac as [kc Hkc_ac].
    destruct (LB16 R H_strong kc a a' c HRaa' Hkc_ac) as [g [Ha'g Hcg]].
    destruct (IH a' b g Hkb_a'b Ha'g) as [d [Hbd Hgd]].
    exists d. split.
    + exact Hbd.
    + exact (reduces_trans R c g d Hcg Hgd).
Qed.

(*******************************************)
(* B.3 :  Commutativity                    *)
(*******************************************)

(* Definition B.17: Commutativity *)
Definition commutes {A} (R S : binary_relation A) : Prop :=
  forall a b c, a =[R]=> b -> a =[S]=> c ->
    exists d, b =[S]=>> d /\ c =[R]=>> d.

(* Definition B.18: Strong Commutativity *)
Definition strongly_commutes {A} (R S : binary_relation A) : Prop :=
  forall a b c, a =[R]=> b -> a =[S]=> c ->
    exists d, b =[S]=> d /\ c =[R]=> d.

(* Lemma B.19: Strong commutativity implies commutativity *)
Lemma strongly_commutes_implies_commutes {A} (R S : binary_relation A) :
  strongly_commutes R S -> commutes R S.
Proof.
  unfold strongly_commutes, commutes. intros.
  pose proof (H a b c H0 H1). 
  destruct H2 as [d [? ?]].
  apply steps_to_reduces in H2, H3.
  exists d. eauto.
Qed.
Abbreviation LB19 := strongly_commutes_implies_commutes.

Lemma reduces_mono {A} (R S : binary_relation A) :
  (forall a b, a =[R]=> b -> a =[S]=> b) ->
  forall a b, a =[R]=>> b -> a =[S]=>> b.
Proof.
  intros Hmono a b [k H].
  revert a b H.
  induction k as [| k IH].
  - intros a b H. simpl in H. subst. apply reduces_refl.
  - intros a b H. simpl in H. destruct H as [e [HRae H]].
    apply reduces_trans with e.
    + apply steps_to_reduces. apply Hmono. exact HRae.
    + apply IH. exact H.
Qed.

Lemma reduces_lift {A} (R S : binary_relation A) :
  (forall a b, a =[R]=> b -> a =[S]=>> b) ->
  forall a b, a =[R]=>> b -> a =[S]=>> b.
Proof.
  intros Hstep a b [k H].
  revert a b H.
  induction k as [| k IH].
  - intros a b H. simpl in H. subst. apply reduces_refl.
  - intros a b H. simpl in H. destruct H as [e [HRae H]].
    apply reduces_trans with e.
    + apply Hstep. exact HRae.
    + apply IH. exact H.
Qed.

(* Lemma B.20: Union *)
Lemma commutes_union {A} (R S1 S2 : binary_relation A) :
  commutes R S1 -> commutes R S2 -> commutes R (S1 \u/ S2).
Proof.
  intros H1 H2 a b c HRab [HS1ac | HS2ac].
  - destruct (H1 a b c HRab HS1ac) as [d [HS1bd HRcd]].
    exists d. split.
    + exact (reduces_mono S1 (S1 \u/ S2) (fun x y H => or_introl H) b d HS1bd).
    + exact HRcd.
  - destruct (H2 a b c HRab HS2ac) as [d [HS2bd HRcd]].
    exists d. split.
    + exact (reduces_mono S2 (S1 \u/ S2) (fun x y H => or_intror H) b d HS2bd).
    + exact HRcd.
Qed.
Abbreviation LB20 := commutes_union.

(* Definition B.21: Strongly Postpones *)
Definition strongly_postpones {A} (R S : binary_relation A) : Prop :=
  forall e e1 e', e =[R]=> e1 -> e1 =[S]=> e' ->
    exists e2, e =[S]=>> e2 /\ e2 =[R]=> e'.

(* Lemma B.22: Postponement *)
Lemma postponement_aux {A} (R S : binary_relation A) : strongly_postpones R S ->
  forall a b c, a =[R]=> b -> b =[S]=>> c -> exists d, a =[S]=>> d /\ d =[R]=> c.
Proof.
  unfold strongly_postpones. intro H_sp.
  intros. destruct H0 as [k].
  revert k a b c H H0.
  induction k.
  - intros. destruct H0.
    exists a. eauto using reduces_refl.
  - intros. destruct H0 as [a' []].
    apply (H_sp a b a' H) in H0.
    destruct H0 as [e2 []].
    specialize (IHk e2 a' c). apply (IHk H2) in H1.
    destruct H1 as [d []].
    eauto using reduces_trans.
Qed.
Abbreviation LB22 := postponement_aux.

Lemma postponement {A} (R S : binary_relation A) : strongly_postpones R S ->
  forall e e', e =[ R \u/ S ]=>> e' ->
    exists e'', e =[S]=>> e'' /\ e'' =[R]=>> e'.
Proof.
  unfold strongly_postpones.
  intros. destruct H0 as [k].
  revert k e e' H0.
  induction k.
  - intros. inversion H0. subst.
    exists e'. eauto using reduces_refl.
  - intros. inversion H0 as [e1 []].
    apply IHk in H2. destruct H2 as [e2 [? ?]].
    destruct H1.
    + pose proof (LB22 R S H e e1 e2).
      destruct (H4 H1 H2) as [e3 []].
      exists e3. apply steps_to_reduces in H6.
      eauto using reduces_trans.
    + apply steps_to_reduces in H1.
      eauto using reduces_trans.
Qed.

(* Definition B.23: Hops *)
Definition hops_after {A} (R S : binary_relation A) : Prop :=
  forall e e1 e', e =[R]=> e1 -> e1 =[S]=> e' ->
    exists e'', e' =[R]=>> e'' /\
      exists e2, e =[S]=> e2 /\ e2 =[R]=>> e''.

(* Lemma B.24 *)
Lemma hops_strip {A} (R S : binary_relation A) : confluent R -> hops_after R S ->
  forall e e1 e', e =[R]=>> e1 -> e1 =[S]=> e' ->
    exists e'', e' =[R]=>> e'' /\
      exists e2, e =[S]=> e2 /\ e2 =[R]=>> e''.
Proof.
  unfold confluent, hops_after.
  intros H_c H_ha.
  intros e e1 e' H.
  destruct H as [n]. revert n e e1 e' H.
  induction n.
  - intros. destruct H.
    exists e'. constructor.
    + apply reduces_refl.
    + exists e'. eauto using reduces_refl.
  - intros. destruct H as [e2 []].
    apply (IHn e2 e1 e') in H0; auto.
    destruct H0 as [e3 []].
    destruct H2 as [e4 []].
    pose proof (H_ha e e2 e4 H H2).
    destruct H4 as [e5 [? [e6 []]]].
    pose proof (H_c e4 e3 e5 H3 H4).
    destruct H7 as [e7 []].
    exists e7. pose proof (reduces_trans R e' e3 e7 H0 H7).
    constructor; auto.
    exists e6. pose proof (reduces_trans R e6 e5 e7 H6 H8).
    constructor; auto.
Qed.
Abbreviation LB24 := hops_strip.


(*******************************************)
(* B.4 :  *-Commutativity                  *)
(*******************************************)

(* Definition B.26: half-commutes*)
Definition half_commutes {A} (R S : binary_relation A) : Prop :=
  forall e e1 e2, e =[R]=> e1 -> e =[S]=> e2 ->
    exists e', e2 =[R]=> e' /\
      exists e3, e1 =[S]=>? e3 /\ e3 =[R]=> e'.

(* Lemma B.30 *)
Lemma half_commutes_strip {A} (R S : binary_relation A) :
  confluent R -> half_commutes R S ->
  forall e e1 e2, e =[R]=>> e1 -> e =[S]=> e2 ->
    exists e', (exists e'', e1 =[S]=>? e'' /\ e'' =[R]=>> e') /\ e2 =[R]=>> e'.
Proof.
  intros Hconf Hhcomm e1 e2 e3 H12.
  destruct H12 as [k1].
  revert k1 e1 e2 e3 H.
  induction k1.
  - intros e1 e2 e3 H12 H13. destruct H12.
    exists e3. constructor; auto using reduces_refl.
    exists e3. auto using reduces_refl, steps_to_skips.
  - intros e1 e2 e3 H12 H13.
    replace (Datatypes.S k1) with (k1 + 1)%nat in H12 by lia.
    apply (steps_k_split R k1 1%nat e1 e2) in H12.
    destruct H12 as [e4 [H14 H42]].
    destruct H42 as [e5 [H45 H52]]. 
    destruct H52.
    pose proof (IHk1 e1 e4 e3 H14 H13).
    destruct H as [e6 [? H36]].
    destruct H as [e7 [H47 H76]]. 
    unfold confluent, half_commutes in *.
    destruct H47 as [| H47]; subst.
    + pose proof (Hconf e7 e5 e6 (steps_to_reduces R e7 e5 H45) H76).
      destruct H as [e8 [H58 H68]].
      exists e8. split; try eapply (reduces_trans R e3 e6 e8); auto.
      exists e5. split; try apply skips_refl; auto.
    + pose proof (Hhcomm e4 e5 e7 H45 H47).
      destruct H as [e8 [H78 [e9 [H59 H98]]]].
      pose proof (Hconf e7 e6 e8 H76 (steps_to_reduces R e7 e8 H78)) as [eA [H6A H8A]].
      exists eA.
      split.
      * exists e9. split; auto.
        apply (reduces_trans R e9 e8 eA (steps_to_reduces R e9 e8 H98) H8A).
      * apply (reduces_trans R e3 e6 eA H36 H6A).
Qed.
Abbreviation LB30 := half_commutes_strip.


(* Lemma B.28 *)
Lemma half_commutes_tiling {A} (R S : binary_relation A) :
  confluent R -> half_commutes R S ->
  forall e e1 e2, e =[R]=>> e1 -> e =[S]=>> e2 ->
    exists e', e1 =[ R \u/ S ]=>> e' /\ e2 =[R]=>> e'.
Proof.
  intros Hconf Hhc.
  pose proof (LB30 R S Hconf Hhc).
  intros e1 e2 e3 H12 H23.
  destruct H23 as [k1 H13].
  revert k1 e1 e2 e3 H12 H13.
  induction k1.
  - intros. destruct H13.
    exists e2. eauto using reduces_refl.
  - intros. destruct H13 as [e4 [H14 H43]].
    pose proof (H e1 e2 e4 H12 H14) as [e5 [[e6 [H62 H25]] H45]].
    pose proof (IHk1 e4 e5 e3 H45 H43) as [e7 [H57 H37]].
    exists e7. split; auto.
    assert (H65 : e6 =[ R \u/ S ]=>> e5).
    { apply (reduces_mono R (R \u/ S) (fun a b H => or_introl H)). exact H25. }
    assert (H67 : e6 =[ R \u/ S ]=>> e7) by (apply reduces_trans with e5; assumption).
    destruct H62 as [Heq | Hstep].
    + subst. exact H67.
    + apply reduces_trans with e6; [apply steps_to_reduces; right; exact Hstep | exact H67].
Qed.
Abbreviation LB28 := half_commutes_tiling.

(* Lemma B.29 *)
Lemma half_commutes_tiling_k {A} (R S : binary_relation A) :
  confluent R -> half_commutes R S ->
  forall k e e1 e2, e =[R]=>> e1 -> e =[(rel_star R);; (rel_pow (S;;rel_star R) k)]=> e2 ->
    exists k' e', (k' <= k)%nat /\ e1 =[(rel_star R);; (rel_pow (S;;rel_star R) k')]=> e' /\ e2 =[R]=>> e'.
Proof.
  intros Hconf Hhc.
  pose proof (LB30 R S Hconf Hhc) as Hhcs.
  induction k as [| k IH]; intros e e1 e2 H1 H2.
  - destruct H2 as [e3 [H3 Heq]]. simpl in Heq. subst e3.
    pose proof (Hconf e e1 e2 H1 H3) as [e4 [H14 H24]].
    exists 0%nat, e4. split; [lia |].
    split; [exists e4; split; [exact H14 | reflexivity] | exact H24].
  - destruct H2 as [e3 [H3 Hrest]].
    destruct Hrest as [e4 [Hblock H42]].
    destruct Hblock as [e5 [H35 H54]].
    pose proof (Hconf e e1 e3 H1 H3) as [e6 [H16 H36]].
    pose proof (Hhcs e3 e6 e5 H36 H35) as [e7 [[e8 [H68 H87]] H57]].
    pose proof (Hconf e5 e4 e7 H54 H57) as [e9 [H49 H79]].
    assert (H42wrap : e4 =[(rel_star R);; (rel_pow (S;;rel_star R) k)]=> e2)
      by (exists e4; split; [apply reduces_refl | exact H42]).
    pose proof (IH e4 e9 e2 H49 H42wrap) as [k1 [eA [Hk1 [H9A H2A]]]].
    destruct H9A as [eB [H9B HBA]].
    destruct H68 as [| H68]; subst.
    + pose proof (reduces_trans R e1 e8 e7 H16 H87) as H17.
      pose proof (reduces_trans R e1 e7 e9 H17 H79) as H19.
      pose proof (reduces_trans R e1 e9 eB H19 H9B) as H1B.
      exists k1, eA. split; [lia |].
      split; [exists eB; split; [exact H1B | exact HBA] | exact H2A].
    + pose proof (reduces_trans R e8 e7 e9 H87 H79) as H89.
      pose proof (reduces_trans R e8 e9 eB H89 H9B) as H8B.
      exists (Nat.succ k1), eA. split; [apply le_n_S; exact Hk1 |].
      split.
      * exists e6. split; [exact H16 |].
        exists eB. split; [exists e8; split; [exact H68 | exact H8B] | exact HBA].
      * exact H2A.
Qed.
Abbreviation LB29 := half_commutes_tiling_k.

(* Lemma B.27 *)
Lemma half_commutes_implies_commutes_union {A} (R S : binary_relation A) :
  confluent R -> half_commutes R S -> commutes R (R \u/ S).
Proof.
  intros Hconf Hhc a b c Hab Hac.
  destruct Hac as [HacR | HacS].
  - destruct (Hconf a b c (steps_to_reduces R a b Hab) (steps_to_reduces R a c HacR)) as [d [Hbd Hcd]].
    exists d. split.
    + apply (reduces_mono R (R \u/ S) (fun p q H => or_introl H)). exact Hbd.
    + exact Hcd.
  - destruct (LB28 R S Hconf Hhc a b c
      (steps_to_reduces R a b Hab) (steps_to_reduces S a c HacS)) as [d [Hbd Hcd]].
    exists d. split; assumption.
Qed.
Abbreviation LB27 := half_commutes_implies_commutes_union.

Lemma union_star_absorb {A} (R S : binary_relation A) :
  forall a b, a =[ R \u/ S ]=>> b <-> a =[ (rel_star R) \u/ S ]=>> b.
Proof.
  intros a b. split.
  - apply reduces_mono. intros x y [HR | HS].
    + left. apply steps_to_reduces. exact HR.
    + right. exact HS.
  - apply reduces_lift. intros x y [HR | HS].
    + apply (reduces_mono R (R \u/ S) (fun p q H => or_introl H)). exact HR.
    + apply steps_to_reduces. right. exact HS.
Qed.

(* (R∪S)* = R*;S;(R*∪S)* ∪ R* *)
Lemma union_star_decompose {A} (R S : binary_relation A) :
  forall a b, a =[ R \u/ S ]=>> b <->
    a =[R]=>> b \/ exists c d, a =[R]=>> c /\ c =[S]=> d /\ d =[ (rel_star R) \u/ S ]=>> b.
Proof.
  intros a b. split.
  - intros [k Hk]. revert a b Hk. induction k as [| k IH].
    + intros a b Hk. simpl in Hk. subst. left. apply reduces_refl.
    + intros a b Hk. simpl in Hk. destruct Hk as [a1 [Hstep Hrest]].
      destruct Hstep as [HR | HS].
      * destruct (IH a1 b Hrest) as [HRstar | [c [d [Hac [Hcd Hdb]]]]].
        -- left. apply reduces_trans with a1; [apply steps_to_reduces; exact HR | exact HRstar].
        -- right. exists c, d. split.
           ++ apply reduces_trans with a1; [apply steps_to_reduces; exact HR | exact Hac].
           ++ exact (conj Hcd Hdb).
      * right. exists a, a1. split; [apply reduces_refl |].
        split; [exact HS | apply (union_star_absorb R S a1 b); exact (steps_k_to_reduces _ k _ _ Hrest)].
  - intros [HR | [c [d [Hac [Hcd Hdb]]]]].
    + apply (reduces_mono R (R \u/ S) (fun x y H => or_introl H)). exact HR.
    + apply (union_star_absorb R S d b) in Hdb.
      apply reduces_trans with c.
      * apply (reduces_mono R (R \u/ S) (fun x y H => or_introl H)). exact Hac.
      * apply reduces_trans with d.
        -- apply steps_to_reduces. right. exact Hcd.
        -- exact Hdb.
Qed.

Lemma union_star_to_hops {A} (R S : binary_relation A) :
  forall a b, a =[ R \u/ S ]=>> b ->
    exists k, a =[(rel_pow (rel_star R;;S) k) ;; rel_star R]=> b.
Proof.
  intros a b [n Hn]. revert a b Hn.
  induction n as [| n IH]; intros a b Hn.
  - simpl in Hn. subst.
    exists 0%nat, b. split; [reflexivity | apply reduces_refl].
  - simpl in Hn. destruct Hn as [e [Hae Heb]].
    destruct (IH e b Heb) as [k' [c [Hec Hcb]]].
    destruct Hae as [HR | HS].
    + destruct k' as [| k''].
      * simpl in Hec. subst c.
        exists 0%nat, a. split; [reflexivity |].
        apply reduces_trans with e; [apply steps_to_reduces; exact HR | exact Hcb].
      * simpl in Hec. destruct Hec as [f [Hef Hfc]].
        destruct Hef as [g [Heg Hgf]].
        exists (Nat.succ k''), c. split; [| exact Hcb].
        simpl. exists f. split; [| exact Hfc].
        exists g. split; [| exact Hgf].
        apply reduces_trans with e; [apply steps_to_reduces; exact HR | exact Heg].
    + exists (Nat.succ k'), c. split; [| exact Hcb].
      simpl. exists e. split; [| exact Hec].
      exists a. split; [apply reduces_refl | exact HS].
Qed.

Lemma pow_comp_shift {A} (R S : binary_relation A) :
  forall k a c b, rel_pow (rel_star R;;S) k a c -> rel_star R c b ->
    a =[(rel_star R);; (rel_pow (S;;rel_star R) k)]=> b.
Proof.
  induction k as [| k IH]; intros a c b Hac Hcb.
  - simpl in Hac. subst c.
    exists b. split; [exact Hcb | reflexivity].
  - destruct Hac as [f [Haf Hfc]].
    destruct Haf as [g [Hag Hgf]].
    destruct (IH f c b Hfc Hcb) as [m [Hfm Hmb]].
    exists g. split; [exact Hag |].
    simpl. exists m. split; [| exact Hmb].
    exists f. split; [exact Hgf | exact Hfm].
Qed.

Lemma pow_comp_shift_rev {A} (R S : binary_relation A) :
  forall k a b, a =[(rel_star R);; (rel_pow (S;;rel_star R) k)]=> b ->
    exists c, rel_pow (rel_star R;;S) k a c /\ rel_star R c b.
Proof.
  induction k as [| k IH]; intros a b Hab.
  - destruct Hab as [m [Ham Hmb]]. simpl in Hmb. subst m.
    exists a. split; [reflexivity | exact Ham].
  - destruct Hab as [g [Hag Hgb]].
    destruct Hgb as [f [Hgf Hfb]].
    destruct Hgf as [w [Hgw Hwf]].
    destruct (IH w b (ex_intro _ f (conj Hwf Hfb))) as [c [Hwc Hcb]].
    exists c. split; [| exact Hcb].
    exists w. split; [| exact Hwc].
    exists g. split; [exact Hag | exact Hgw].
Qed.

(* Lemma B.25 (half_commutes added) *)
Lemma hops_union {A} (R S : binary_relation A) : confluent R -> hops_after R S -> half_commutes R S ->
  forall e e', e =[ R \u/ S ]=>> e' ->
    exists e'', (exists e1, e =[S]=>> e1 /\ e1 =[R]=>> e'') /\ e' =[R]=>> e''.
Proof.
  intros Hconf Hha Hhc e1 e2 H12.
  apply union_star_to_hops in H12 as [k H12].
  pose proof (LB24 R S Hconf Hha) as Hhs.
  pose proof (LB29 R S Hconf Hhc) as Hctk.
  revert e1 e2 H12.
  induction k using Wf_nat.lt_wf_ind.
  destruct k; intros e1 e2 H12.
  - destruct H12 as [e3 [H13 H32]]. simpl in H13. subst e3.
    exists e2. eauto using reduces_refl.
  - destruct H12 as [e3 [H13 H32]].
    destruct H13 as [e4 [H14 H43]].
    destruct H14 as [e5 [H15 H54]].
    pose proof (Hhs e1 e5 e4 H15 H54) as [e6 [H46 [e7 [H17 H76]]]].
    pose proof (pow_comp_shift R S k e4 e3 e2 H43 H32) as H42.
    pose proof (Hctk k e4 e6 e2 H46 H42) as [k1 [e8 [Hk1 [H68 H28]]]].
    destruct H68 as [e9 [H69 H98]].
    pose proof (reduces_trans R e7 e6 e9 H76 H69) as H79.
    pose proof (ex_intro (fun m => rel_star R e7 m /\ rel_pow (S;;rel_star R) k1 m e8) e9 (conj H79 H98)) as H78.
    apply (pow_comp_shift_rev R S k1 e7 e8) in H78.
    pose proof (H k1 (proj2 (Nat.lt_succ_r k1 k) Hk1) e7 e8 H78) as [eA [[eB [H7B HBA]] H8A]].
    exists eA. split.
    + exists eB. split.
      * exact (reduces_trans S e1 e7 eB (steps_to_reduces S e1 e7 H17) H7B).
      * exact HBA.
    + exact (reduces_trans R e2 e8 eA H28 H8A).
Qed.
Abbreviation LB25 := hops_union.

(* Definition B.31: *-Commutativity *)
Definition star_commutes {A} (R S : binary_relation A) : Prop :=
  forall a b c, a =[R]=> b -> a =[S]=> c ->
    exists d, b =[S]=>> d /\ c =[R]=>? d.

(* Lemma B.32 *)
Lemma star_commutes_strip {A} (R S : binary_relation A) :
  star_commutes R S ->
  forall a b c, a =[R]=> b -> a =[S]=>> c ->
    exists d, b =[S]=>> d /\ c =[R]=>? d.
Proof.
  intros Hsc a b c HRab Hac.
  destruct Hac as [n Hac].
  revert a b c HRab Hac.
  induction n as [| n IH]; intros a b c HRab Hac.
  - simpl in Hac. subst c.
    exists b. split; [apply reduces_refl | right; exact HRab].
  - replace (Datatypes.S n) with (n + 1)%nat in Hac by lia.
    apply (steps_k_split S n 1%nat a c) in Hac.
    destruct Hac as [c' [Hac' Hc'c]].
    destruct Hc'c as [c'' [Hc'c'' Heq]].
    destruct Heq.
    destruct (IH a b c' HRab Hac') as [d' [Hbd' Hc'd']].
    destruct Hc'd' as [Heq2 | Hstep].
    + subst d'.
      exists c''. split; [exact (reduces_trans S b c' c'' Hbd' (steps_to_reduces S c' c'' Hc'c'')) | left; reflexivity].
    + destruct (Hsc c' d' c'' Hstep Hc'c'') as [d [Hd'd Hcd]].
      exists d. split; [exact (reduces_trans S b d' d Hbd' Hd'd) | exact Hcd].
Qed.
Abbreviation LB32 := star_commutes_strip.

(* Lemma B.33 *)
Lemma star_commutes_strip2 {A} (R S : binary_relation A) :
  star_commutes R S ->
  forall a b c, a =[R]=>> b -> a =[S]=> c ->
    exists d, b =[S]=>> d /\ c =[R]=>> d.
Proof.
  intros Hsc a b c Hab HSac.
  destruct Hab as [n Hab].
  revert a b c Hab HSac.
  induction n as [| n IH]; intros a b c Hab HSac.
  - simpl in Hab. subst b.
    exists c. split; [apply steps_to_reduces; exact HSac | apply reduces_refl].
  - replace (Datatypes.S n) with (n + 1)%nat in Hab by lia.
    apply (steps_k_split R n 1%nat a b) in Hab.
    destruct Hab as [b' [Hab' Hb'b]].
    destruct Hb'b as [b'' [Hb'b'' Heq]].
    destruct Heq.
    destruct (IH a b' c Hab' HSac) as [d' [Hb'd' Hcd']].
    destruct (LB32 R S Hsc b' b'' d' Hb'b'' Hb'd') as [d [Hbd Hd'd]].
    exists d. split; [exact Hbd |].
    exact (reduces_trans R c d' d Hcd' (skips_to_reduces R d' d Hd'd)).
Qed.
Abbreviation LB33 := star_commutes_strip2.

Lemma star_commutes_strip3 {A} (R S : binary_relation A) :
  star_commutes R S ->
  forall a b c, a =[R]=> b -> a =[S]=>> c ->
    exists d, b =[S]=>> d /\ c =[R]=>> d.
Proof.
  intros Hsc a b c HRab Hac.
  destruct Hac as [n Hac].
  revert a b c HRab Hac.
  induction n as [| n IH]; intros a b c HRab Hac.
  - simpl in Hac. subst c.
    exists b. split; [apply reduces_refl | apply steps_to_reduces; exact HRab].
  - replace (Datatypes.S n) with (n + 1)%nat in Hac by lia.
    apply (steps_k_split S n 1%nat a c) in Hac.
    destruct Hac as [c' [Hac' Hc'c]].
    destruct Hc'c as [c'' [Hc'c'' Heq]].
    destruct Heq.
    destruct (IH a b c' HRab Hac') as [d' [Hbd' Hc'd']].
    destruct (LB33 R S Hsc c' d' c'' Hc'd' Hc'c'') as [d [Hd'd Hcd]].
    exists d. split; [exact (reduces_trans S b d' d Hbd' Hd'd) | exact Hcd].
Qed.

(* Lemma B.34 *)
Lemma star_commutes_implies_commutes {A} (R S : binary_relation A) :
  star_commutes R S -> commutes R S.
Proof.
  intros Hsc a b c HRab HSac.
  exact (star_commutes_strip3 R S Hsc a b c HRab (steps_to_reduces S a c HSac)).
Qed.
Abbreviation LB34 := star_commutes_implies_commutes.

(*******************************************)
(* B.5 :  Commutativity and Confluence     *)
(*******************************************)

Lemma sc_strip1 {A} (R S : binary_relation A) : strongly_commutes R S ->
  forall a b c, R a b -> a =[S]=>> c -> exists d, b =[S]=>> d /\ c =[R]=>> d.
Proof.
  intros Hsc a b c HRab Hac.
  destruct Hac as [n Hac]. revert a b c HRab Hac.
  induction n as [| n IH]; intros a b c HRab Hac.
  - simpl in Hac. subst c.
    exists b. split; [apply reduces_refl | apply steps_to_reduces; exact HRab].
  - simpl in Hac. destruct Hac as [a1 [Ha1 Hrest]].
    destruct (Hsc a b a1 HRab Ha1) as [d1 [Hbd1 Ha1d1]].
    destruct (IH a1 d1 c Ha1d1 Hrest) as [d [Hd1d Hcd]].
    exists d. split; [| exact Hcd].
    apply reduces_trans with d1; [apply steps_to_reduces; exact Hbd1 | exact Hd1d].
Qed.

Lemma sc_lift {A} (R S : binary_relation A) : strongly_commutes R S ->
  forall a b c, a =[R]=>> b -> a =[S]=>> c -> exists d, b =[S]=>> d /\ c =[R]=>> d.
Proof.
  intros Hsc a b c Hab Hac.
  destruct Hab as [n Hab]. revert a b c Hab Hac.
  induction n as [| n IH]; intros a b c Hab Hac.
  - simpl in Hab. subst b.
    exists c. split; [exact Hac | apply reduces_refl].
  - replace (Datatypes.S n) with (n + 1)%nat in Hab by lia.
    apply (steps_k_split R n 1%nat a b) in Hab.
    destruct Hab as [b' [Hab' Hb'b]].
    destruct Hb'b as [b'' [Hb'b'' Heq]]. destruct Heq.
    destruct (IH a b' c Hab' Hac) as [d' [Hb'd' Hcd']].
    destruct (sc_strip1 R S Hsc b' b'' d' Hb'b'' Hb'd') as [d [Hbd Hd'd]].
    exists d. split; [exact Hbd |].
    exact (reduces_trans R c d' d Hcd' Hd'd).
Qed.

Lemma sc_lift_sym {A} (R S : binary_relation A) : strongly_commutes R S ->
  forall x y z, x =[S]=>> y -> x =[R]=>> z -> exists w, y =[R]=>> w /\ z =[S]=>> w.
Proof.
  intros Hsc x y z Hxy Hxz.
  destruct (sc_lift R S Hsc x z y Hxz Hxy) as [w [Hzw Hyw]].
  exists w. split; assumption.
Qed.

Lemma union_confluent_aux {A} (R S : binary_relation A) : confluent R -> strongly_commutes R S ->
  forall k e e1 e2, e =[R]=>> e1 -> e =[(rel_star R);; (rel_pow (S;;rel_star R) k)]=> e2 ->
    exists e', e1 =[R\u/S]=>> e' /\ e2 =[R]=>> e'.
Proof.
  intros HconfR Hsc.
  induction k as [| k IH]; intros e e1 e2 H1 H2.
  - destruct H2 as [m [Hm Heq]]. simpl in Heq. subst m.
    destruct (HconfR e e1 e2 H1 Hm) as [e' [H1' H2']].
    exists e'. split; [apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact H1' | exact H2'].
  - destruct H2 as [p [Hp Hrest]].
    destruct Hrest as [q [Hblock Htail]].
    destruct Hblock as [s [Hps Hsq]].
    destruct (HconfR e e1 p H1 Hp) as [h [H1h Hph]].
    destruct (sc_lift R S Hsc p h s Hph (steps_to_reduces S p s Hps)) as [f [Hhf Hsf]].
    destruct (HconfR s f q Hsf Hsq) as [g [Hfg Hqg]].
    assert (Hqtile : q =[(rel_star R);; (rel_pow (S;;rel_star R) k)]=> e2)
      by (exists q; split; [apply reduces_refl | exact Htail]).
    destruct (IH q g e2 Hqg Hqtile) as [e' [Hge' He2e']].
    exists e'. split; [| exact He2e'].
    apply reduces_trans with h; [apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact H1h |].
    apply reduces_trans with f; [apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact Hhf |].
    apply reduces_trans with g; [apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact Hfg | exact Hge'].
Qed.

Lemma union_confluent_aux_S {A} (R S : binary_relation A) : confluent S -> strongly_commutes R S ->
  forall k e e1 e2, e =[S]=>> e1 -> e =[(rel_star S);; (rel_pow (R;;rel_star S) k)]=> e2 ->
    exists e', e1 =[R\u/S]=>> e' /\ e2 =[S]=>> e'.
Proof.
  intros HconfS Hsc.
  induction k as [| k IH]; intros e e1 e2 H1 H2.
  - destruct H2 as [m [Hm Heq]]. simpl in Heq. subst m.
    destruct (HconfS e e1 e2 H1 Hm) as [e' [H1' H2']].
    exists e'. split; [apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact H1' | exact H2'].
  - destruct H2 as [p [Hp Hrest]].
    destruct Hrest as [q [Hblock Htail]].
    destruct Hblock as [s [Hps Hsq]].
    destruct (HconfS e e1 p H1 Hp) as [h [H1h Hph]].
    destruct (sc_lift_sym R S Hsc p h s Hph (steps_to_reduces R p s Hps)) as [f [Hhf Hsf]].
    destruct (HconfS s f q Hsf Hsq) as [g [Hfg Hqg]].
    assert (Hqtile : q =[(rel_star S);; (rel_pow (R;;rel_star S) k)]=> e2)
      by (exists q; split; [apply reduces_refl | exact Htail]).
    destruct (IH q g e2 Hqg Hqtile) as [e' [Hge' He2e']].
    exists e'. split; [| exact He2e'].
    apply reduces_trans with h; [apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact H1h |].
    apply reduces_trans with f; [apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact Hhf |].
    apply reduces_trans with g; [apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact Hfg | exact Hge'].
Qed.

Lemma ru_swap {A} (R S : binary_relation A) : forall a b, a =[R\u/S]=>> b -> a =[S\u/R]=>> b.
Proof. apply reduces_mono. intros x y [H | H]; [right | left]; exact H. Qed.

Lemma ru_strip {A} (R S : binary_relation A) : confluent R -> confluent S -> strongly_commutes R S ->
  forall n a b c, a =[R\u/S]=> b -> steps_k (R\u/S) n a c -> exists d, b =[R\u/S]=>> d /\ c =[R\u/S]=>> d.
Proof.
  intros HconfR HconfS Hsc.
  induction n as [| n IH]; intros a b c Hab Hac.
  - simpl in Hac. subst c.
    exists b. split; [apply reduces_refl | apply steps_to_reduces; exact Hab].
  - simpl in Hac. destruct Hac as [a1 [Ha1 Hrest]].
    destruct Hab as [HRab | HSab]; destruct Ha1 as [HRa1 | HSa1].
    + destruct (HconfR a b a1 (steps_to_reduces R a b HRab) (steps_to_reduces R a a1 HRa1)) as [g [Hbg Ha1g]].
      pose proof (union_star_to_hops R S _ _ (steps_k_to_reduces (R\u/S) n a1 c Hrest)) as [k [c1 [Hc1 Hcc1]]].
      pose proof (pow_comp_shift R S k a1 c1 c Hc1 Hcc1) as Ha1c.
      destruct (union_confluent_aux R S HconfR Hsc k a1 g c Ha1g Ha1c) as [e' [Hge' Hce']].
      exists e'. split.
      * apply reduces_trans with g; [apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact Hbg | exact Hge'].
      * apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact Hce'.
    + destruct (sc_lift R S Hsc a b a1 (steps_to_reduces R a b HRab) (steps_to_reduces S a a1 HSa1)) as [g [Hbg Ha1g]].
      pose proof (union_star_to_hops R S _ _ (steps_k_to_reduces (R\u/S) n a1 c Hrest)) as [k [c1 [Hc1 Hcc1]]].
      pose proof (pow_comp_shift R S k a1 c1 c Hc1 Hcc1) as Ha1c.
      destruct (union_confluent_aux R S HconfR Hsc k a1 g c Ha1g Ha1c) as [e' [Hge' Hce']].
      exists e'. split.
      * apply reduces_trans with g; [apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact Hbg | exact Hge'].
      * apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact Hce'.
    + destruct (sc_lift_sym R S Hsc a b a1 (steps_to_reduces S a b HSab) (steps_to_reduces R a a1 HRa1)) as [g [Hbg Ha1g]].
      pose proof (union_star_to_hops S R _ _ (ru_swap R S a1 c (steps_k_to_reduces (R\u/S) n a1 c Hrest))) as [k [c1 [Hc1 Hcc1]]].
      pose proof (pow_comp_shift S R k a1 c1 c Hc1 Hcc1) as Ha1c.
      destruct (union_confluent_aux_S R S HconfS Hsc k a1 g c Ha1g Ha1c) as [e' [Hge' Hce']].
      exists e'. split.
      * apply reduces_trans with g; [apply (reduces_mono R (R\u/S) (fun x y H => or_introl H)); exact Hbg | exact Hge'].
      * apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact Hce'.
    + destruct (HconfS a b a1 (steps_to_reduces S a b HSab) (steps_to_reduces S a a1 HSa1)) as [g [Hbg Ha1g]].
      pose proof (union_star_to_hops S R _ _ (ru_swap R S a1 c (steps_k_to_reduces (R\u/S) n a1 c Hrest))) as [k [c1 [Hc1 Hcc1]]].
      pose proof (pow_comp_shift S R k a1 c1 c Hc1 Hcc1) as Ha1c.
      destruct (union_confluent_aux_S R S HconfS Hsc k a1 g c Ha1g Ha1c) as [e' [Hge' Hce']].
      exists e'. split.
      * apply reduces_trans with g; [apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact Hbg | exact Hge'].
      * apply (reduces_mono S (R\u/S) (fun x y H => or_intror H)); exact Hce'.
Qed.

(* Lemma B.35 (Commutativity) *)
Lemma commutativity {A} (R S : binary_relation A) :
  confluent R -> confluent S -> strongly_commutes R S -> confluent (R \u/ S).
Proof.
  intros HconfR HconfS Hsc a b c [kb Hab] Hac.
  revert a b c Hab Hac.
  induction kb as [| kb IH].
  - intros a b c Hab Hac. simpl in Hab. subst.
    exists c. split. exact Hac. apply reduces_refl.
  - intros a b c Hab Hac.
    simpl in Hab. destruct Hab as [a' [HRaa' Hkb_a'b]].
    destruct Hac as [kc Hkc_ac].
    destruct (ru_strip R S HconfR HconfS Hsc kc a a' c HRaa' Hkc_ac) as [g [Ha'g Hcg]].
    destruct (IH a' b g Hkb_a'b Ha'g) as [d [Hbd Hgd]].
    exists d. split.
    + exact Hbd.
    + exact (reduces_trans (R\u/S) c g d Hcg Hgd).
Qed.
Abbreviation LB35 := commutativity.

Lemma strongly_commutes_sym {A} (R S : binary_relation A) : strongly_commutes R S -> strongly_commutes S R.
Proof.
  intros H a b c HSab HRac.
  destruct (H a c b HRac HSab) as [d [Hcd Hbd]].
  exists d. split; [exact Hbd | exact Hcd].
Qed.

Lemma strongly_commutes_union_left {A} (R1 R2 S : binary_relation A) :
  strongly_commutes R1 S -> strongly_commutes R2 S -> strongly_commutes (R1 \u/ R2) S.
Proof.
  intros H1 H2 a b c [HR1ab | HR2ab] HSac.
  - destruct (H1 a b c HR1ab HSac) as [d [Hbd Hcd]].
    exists d. split; [exact Hbd | left; exact Hcd].
  - destruct (H2 a b c HR2ab HSac) as [d [Hbd Hcd]].
    exists d. split; [exact Hbd | right; exact Hcd].
Qed.

Fixpoint union_n {A} (f : nat -> binary_relation A) (n : nat) : binary_relation A :=
  match n with
  | 0%nat => f 0%nat
  | S n' => union_n f n' \u/ f (S n')
  end.

Lemma union_n_commutes {A} (f : nat -> binary_relation A) (m : nat) :
  forall n, (forall i, (i <= n)%nat -> strongly_commutes (f i) (f m)) -> strongly_commutes (union_n f n) (f m).
Proof.
  induction n as [| n IH]; intros H.
  - simpl. apply H. lia.
  - simpl. apply strongly_commutes_union_left.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

(* Lemma B.36 (N-Commutativity) *)
Lemma n_commutativity {A} (f : nat -> binary_relation A) :
  forall n,
    (forall i, (i <= n)%nat -> confluent (f i)) ->
    (forall i j, (i < j)%nat -> (j <= n)%nat -> strongly_commutes (f i) (f j)) ->
    confluent (union_n f n).
Proof.
  induction n as [| n IH]; intros Hconf Hcomm.
  - simpl. apply Hconf. lia.
  - simpl.
    apply LB35.
    + apply IH.
      * intros i Hi. apply Hconf. lia.
      * intros i j Hij Hjn. apply Hcomm; lia.
    + apply Hconf. lia.
    + apply union_n_commutes. intros i Hi. apply Hcomm; lia.
Qed.
Abbreviation LB36 := n_commutativity.

(*******************************************)
(* B.6 :  Confluent Kernels                *)
(*******************************************)

(* Definition B.37: Kernel *)
Definition kernel {A} (S R : binary_relation A) : Prop :=
  (forall a b, S a b -> R a b) /\
  (forall a b, R a b -> exists c, a =[S]=>> c /\ b =[S]=>> c).

(* Lemma B.38: Kernel-Steps *)
Lemma kernel_steps {A} (S R : binary_relation A) :
  kernel S R -> confluent S -> forall a b, a =[R]=>> b -> exists c, a =[S]=>> c /\ b =[S]=>> c.
Proof.
  intros [Hsub Hker] HconfS a b Hab.
  destruct Hab as [n Hab]. revert a b Hab.
  induction n as [| n IH]; intros a b Hab.
  - simpl in Hab. subst b.
    exists a. split; apply reduces_refl.
  - replace (Datatypes.S n) with (n + 1)%nat in Hab by lia.
    apply (steps_k_split R n 1%nat a b) in Hab.
    destruct Hab as [b' [Hab' Hb'b]].
    destruct Hb'b as [b'' [Hb'b'' Heq]]. destruct Heq.
    destruct (IH a b' Hab') as [c [Hac Hb'c]].
    destruct (Hker b' b'' Hb'b'') as [c' [Hb'c' Hb''c']].
    destruct (HconfS b' c c' Hb'c Hb'c') as [c'' [Hcc'' Hc'c'']].
    exists c''. split.
    + exact (reduces_trans S a c c'' Hac Hcc'').
    + exact (reduces_trans S b'' c' c'' Hb''c' Hc'c'').
Qed.
Abbreviation LB38 := kernel_steps.

(* Theorem B.39: Kernel Confluence *)
Theorem kernel_confluence {A} (S R : binary_relation A) :
  kernel S R -> confluent S -> confluent R.
Proof.
  intros Hkernel HconfS a b1 b2 Hab1 Hab2.
  destruct Hkernel as [Hsub Hker].
  destruct (kernel_steps S R (conj Hsub Hker) HconfS a b1 Hab1) as [c1 [Hac1 Hb1c1]].
  destruct (kernel_steps S R (conj Hsub Hker) HconfS a b2 Hab2) as [c2 [Hac2 Hb2c2]].
  destruct (HconfS a c1 c2 Hac1 Hac2) as [c [Hc1c Hc2c]].
  exists c. split.
  - exact (reduces_trans R b1 c1 c
      (reduces_mono S R Hsub b1 c1 Hb1c1)
      (reduces_mono S R Hsub c1 c Hc1c)).
  - exact (reduces_trans R b2 c2 c
      (reduces_mono S R Hsub b2 c2 Hb2c2)
      (reduces_mono S R Hsub c2 c Hc2c)).
Qed.
Abbreviation LB39 := kernel_confluence.
