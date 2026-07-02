From Stdlib Require Import ZArith List PeanoNat.
Import ListNotations.
From VersRocq Require Import Syntax Context.
Open Scope Z_scope.
Open Scope vc_scope.

(* Helper Functions *)

Fixpoint fvs_e (e : expr) : list var :=
  match e with
  | ValE v        => fvs_v v
  | SeqE q e'     => fvs_eqn q ++ fvs_e e'
  | ExE x e'      => List.remove Nat.eq_dec x (fvs_e e')
  | FailE         => []
  | ChoiceE e1 e2 => fvs_e e1 ++ fvs_e e2
  | AppE v1 v2    => fvs_v v1 ++ fvs_v v2
  | OneE e'       => fvs_e e'
  | AllE e'       => fvs_e e'
  end
with fvs_v (v : val) : list var :=
  match v with
  | VarV x => [x]
  | HnfV h => fvs_hnf h
  end
with fvs_hnf (h : hnf) : list var :=
  match h with
  | IntH _   => []
  | OpH  _   => []
  | TupH vs  => List.flat_map fvs_v vs
  | LamH x e => List.remove Nat.eq_dec x (fvs_e e)
  end
with fvs_eqn (q : eqn) : list var :=
  match q with
  | ExprEqn e  => fvs_e e
  | EqEqn v e  => fvs_v v ++ fvs_e e
  end.

Fixpoint fvs_vs (vs : list val) : list var :=
  match vs with
  | [] => []
  | v :: rest => (fvs_v v) ++ (fvs_vs rest)
  end.

Fixpoint fvs_xctx (X : xctx) : list var :=
  match X with
  | XHole => []
  | XEqR v X' e => fvs_v v ++ fvs_xctx X' ++ fvs_e e
  | XSeqL X' e => fvs_xctx X' ++ fvs_e e
  | XSeqR q X' => fvs_eqn q ++ fvs_xctx X'
  end.


Fixpoint subst_val (v' : val) (v : val) (x : var) : val :=
  match v' with
  | VarV y => if Nat.eqb x y then v else VarV y
  | HnfV h => HnfV (subst_hnf h v x)
  end

with subst_hnf (h : hnf) (v : val) (x : var) : hnf :=
  match h with
  | IntH k => IntH k
  | OpH op => OpH op
  | TupH vs => TupH (List.map (fun v' => subst_val v' v x) vs)
  | LamH y e =>
      if Nat.eqb x y then LamH y e
      else LamH y (subst_expr e v x)
  end

with subst_expr (e : expr) (v : val) (x : var) : expr :=
  match e with
  | ValE v' => ValE (subst_val v' v x)
  | SeqE q e' => (subst_eqn q v x); (subst_expr e' v x)
  | ExE y e' =>
      if Nat.eqb x y then ExE y e'
      else ExE y (subst_expr e' v x)
  | FailE => FailE
  | ChoiceE e1 e2 => (subst_expr e1 v x) <|> (subst_expr e2 v x)
  | AppE v1 v2 => AppE (subst_val v1 v x) (subst_val v2 v x)
  | OneE e' => OneE (subst_expr e' v x)
  | AllE e' => AllE (subst_expr e' v x)
  end

with subst_eqn (q : eqn) (v : val) (x : var) : eqn :=
  match q with
  | ExprEqn e => ExprEqn (subst_expr e v x)
  | EqEqn v' e => EqEqn (subst_val v' v x) (subst_expr e v x)
  end.

Fixpoint subst_xctx (X : xctx) (v : val) (x : var) : xctx :=
  match X with
  | XHole => XHole
  | XEqR v' X' e =>
      XEqR (subst_val v' v x) (subst_xctx X' v x) (subst_expr e v x)
  | XSeqL X' e =>
      XSeqL (subst_xctx X' v x) (subst_expr e v x)
  | XSeqR q X' =>
      XSeqR (subst_eqn q v x) (subst_xctx X' v x)
  end.

Fixpoint aux_app_tup (x : var) (i : Z) (vs : list val) : expr :=
  match vs with
  | [] => FailE
  | v :: nil => (EqEqn x i); (ValE v)
  | v :: vs' =>
    ((EqEqn x i); v) <|> (aux_app_tup x (i + 1) vs')
  end.

Fixpoint aux_uni_tup (vs1 vs2 : list val) (e : expr) : expr :=
  match vs1, vs2 with
  | [], [] => e
  | v1 :: vs1', v2 :: vs2' =>
    match aux_uni_tup vs1' vs2' e with
    | FailE => FailE
    | rest => (EqEqn v1 v2); rest
    end
  | _, _ => FailE
  end.

Definition aux_uni_fail (h1 h2 : hnf) : Prop :=
  match h1, h2 with
  | IntH k1, IntH k2 => k1 <> k2
  | TupH vs1, TupH vs2 => length vs1 <> length vs2
  | LamH _ _, LamH _ _ => False
  | LamH _ _, _ => False
  | _, LamH _ _ => False
  | _, _ => True
  end.

Fixpoint aux_all_choice (e : expr) : option (list val) :=
  match e with
  | ValE v => Some [v]
  | ChoiceE e1 e2 =>
    match aux_all_choice e1, aux_all_choice e2 with
    | Some vs1, Some vs2 => Some (vs1 ++ vs2)
    | _, _ => None
    end
  | _ => None
  end.

(* rewriting rules *)

Inductive verse_step : expr -> expr -> Prop :=
  | AppAdd : forall (k1 k2 : Z),
      verse_step (AppE Add (TupH ((HnfV k1) :: (HnfV k2) :: nil))) (k1 + k2)
  | AppGt : forall (k1 k2 : Z),
      k2 < k1 ->
      verse_step (AppE Gt (TupH ((HnfV k1) :: (HnfV k2) :: nil))) k1
  | AppGtFail : forall (k1 k2 : Z),
      k1 <= k2 ->
      verse_step (AppE Gt (TupH ((HnfV k1) :: (HnfV k2) :: nil))) FailE
  | AppBeta : forall (x : var) (e : expr) (v : val),
      ~ In x (fvs_v v) ->
      verse_step (AppE (LamH x e) v)
          (ExE x ((EqEqn x v); e))
  | AppTup : forall (x : var) (vs : list val) (v : val),
      vs <> [] ->
      ~ In x (fvs_vs (v :: vs)) ->
      verse_step (AppE (TupH vs) v)
           (ExE x ((EqEqn x v); (aux_app_tup x 0 vs)))
  | AppTup0 : forall (v : val),
      verse_step (AppE (TupH []) v) FailE


  | UniLit : forall (k : Z) (e : expr),
      verse_step ((EqEqn k k); e) e
  | UniTup : forall (vs vs' : list val) (e : expr),
      verse_step ((EqEqn (TupH vs) (TupH vs')); e) (aux_uni_tup vs vs' e)
  | UniFail : forall (h1 h2 : hnf) (e : expr),
      aux_uni_fail h1 h2 ->
      verse_step ((EqEqn h1 h2); e) FailE
  | UniOccurs : forall (x : var) (V : vctx) (e : expr),
      verse_step ((EqEqn x (vfill V x)); e)
        (match V with
          | VHole => e
          | VTup _ _ => FailE
          end)
  | UniSubst : forall (X : xctx) (x : var) (v : val) (e : expr),
      (forall V : vctx, v <> vfill V x) ->
      verse_step (xfill X ((EqEqn x v); e))
           (xfill (subst_xctx X v x) ((EqEqn x v); (subst_expr e v x)))
  | UniHnfSwap : forall (h : hnf) (v : val) (e : expr),
      verse_step ((EqEqn h v); e) ((EqEqn v h); e)
  | UniVarSwap : forall (x y : var) (e : expr),
      vlt x y ->
      verse_step ((EqEqn (VarV y) (VarV x)); e)
          ((EqEqn (VarV x) (VarV y)); e)
  | UniSeqSwap : forall (q : eqn) (x : var) (v : val) (e : expr),
      ~(match q with
        | EqEqn (VarV y) (ValE _) => vleb y x = true
        | _ => False
        end) ->
      verse_step (q; (EqEqn x v); e) ((EqEqn x v); q; e)


  | ElimVal : forall (v : val) (e : expr),
      verse_step (SeqE v e) e
  | ElimExi : forall (x : var) (e : expr),
      ~ In x (fvs_e e) ->
      verse_step (ExE x e) e
  | ElimEqn : forall (x : var) (X : xctx) (v : val) (e : expr),
      ~ In x (fvs_e (xfill X e)) ->
      ~ In x (fvs_v v) ->
      verse_step (ExE x (xfill X (SeqE (EqEqn x v) e))) (xfill X e)
  | ElimFail : forall (X : xctx),
      verse_step (xfill X FailE) FailE


  | ExiFloat : forall (X : xctx) (x : var) (e : expr),
      ~ In x (fvs_xctx X) ->
      verse_step (xfill X (ExE x e)) (ExE x (xfill X e))
  | SeqAssoc : forall (q : eqn) (e1 e2 : expr),
      verse_step ((q; e1); e2) (q; (e1; e2))
  | EqnFloat : forall (v : val) (q : eqn) (e1 e2 : expr),
      verse_step ((EqEqn v (q; e1)); e2) (q; ((EqEqn v e1); e2))
  | ExiSwap : forall (x y : var) (e : expr),
      verse_step (ExE x (ExE y e)) (ExE y (ExE x e))


  | OneFail : verse_step (OneE FailE) FailE
  | OneValue : forall (v : val), verse_step (OneE v) v
  | OneChoice : forall (v : val) (e : expr),
      verse_step (OneE (v <|> e)) v
  | AllFail : verse_step (AllE FailE) (TupH nil)
  | AllValue : forall (v : val), verse_step (AllE v) (TupH [v])
  | AllChoice : forall (e : expr) (vs : list val),
      aux_all_choice e = Some vs ->
      verse_step (AllE e) (TupH vs)
  | ChooseR : forall (e : expr), verse_step (FailE <|> e) e
  | ChooseL : forall (e : expr), verse_step (e <|> FailE) e
  | ChooseAssoc : forall (e1 e2 e3 : expr),
      verse_step ((e1 <|> e2) <|> e3) (e1 <|> (e2 <|> e3))
  | Choose : forall (SX : sx) (CX : cx) (e1 e2 : expr),
      verse_step (sxfill SX (cxfill CX (e1 <|> e2))) (sxfill SX ((cxfill CX e1) <|> (cxfill CX e2)))
.
