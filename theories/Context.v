From VersRocq Require Import Syntax.

Inductive xctx : Type :=
  | XHole  : xctx                           (* []        *)
  | XEqR   : val -> xctx -> expr -> xctx    (* v = X; e  *)
  | XSeqL  : xctx -> expr -> xctx           (* X; e      *)
  | XSeqR  : eqn  -> xctx -> xctx.          (* eq; X     *)

Fixpoint xfill (X : xctx) (e : expr) : expr :=
  match X with
  | XHole         => e
  | XEqR v X' e' => (EqEqn v (xfill X' e)); e'
  | XSeqL X' e'  => (ExprEqn (xfill X' e)); e'
  | XSeqR q X'   => q; (xfill X' e)
  end.

Inductive vctx : Type :=
  | VHole : vctx                                (* []             *)
  | VTup  : list val -> list val -> vctx.       (* <vs1, V, vs2>  *)

Definition vfill (V : vctx) (v : val) : val :=
  match V with
  | VHole        => v
  | VTup vs1 vs2 => HnfV (TupH (vs1 ++ (v :: vs2)))
  end.

Inductive sc : Type :=
  | SCHole  : sc                       (* []          *)
  | SCLeft  : sc   -> expr -> sc       (* SC <|> e    *)
  | SCRight : expr -> sc   -> sc.      (* e  <|> SC   *)

Inductive sx : Type :=
  | SXOne : sc -> sx                   (* one{SC} *)
  | SXAll : sc -> sx.                  (* all{SC} *)

Fixpoint scfill (SC : sc) (e : expr) : expr :=
  match SC with
  | SCHole          => e
  | SCLeft  SC' e'  => (scfill SC' e) <|> e'
  | SCRight e' SC'  => e' <|> (scfill SC' e)
  end.

Definition sxfill (SX : sx) (e : expr) : expr :=
  match SX with
  | SXOne s => OneE (scfill s e)
  | SXAll s => AllE (scfill s e)
  end.

Inductive cx : Type :=
  | CXHole  : cx
  | CXEqR   : val    -> cx -> expr -> cx   (* v=CX; e   *)
  | CXSeqL  : cx     -> expr -> cx         (* CX; e     *)
  | CXSeqR  : cfeqn  -> cx -> cx           (* cfeqn; CX *)
  | CXEx    : var    -> cx -> cx           (* Ex.CX     *)

with cfexpr : Type :=
  | CEVal  : val    -> cfexpr             (* v           *)
  | CESeqR : cfeqn  -> cfexpr -> cfexpr   (* cfeqn; ce   *)
  | CEOne  : expr   -> cfexpr             (* one{e}      *)
  | CEAll  : expr   -> cfexpr             (* all{e}      *)
  | CEEx   : var    -> cfexpr -> cfexpr   (* Ex.ce       *)
  | CEOp   : primop -> val -> cfexpr      (* op(v)       *)

with cfeqn : Type :=
  | CEQExpr : cfexpr -> cfeqn           (* ce          *)
  | CEQEq   : val -> cfexpr -> cfeqn.   (* v=ce        *)

Fixpoint ce_to_expr (ce : cfexpr) : expr :=
  match ce with
  | CEVal v        => ValE v
  | CESeqR ceq ce' =>(ceq_to_eqn ceq); (ce_to_expr ce')
  | CEOne e        => OneE e
  | CEAll e        => AllE e
  | CEEx x ce'     => ExE x (ce_to_expr ce')
  | CEOp op v      => AppE (HnfV (OpH op)) v
  end

with ceq_to_eqn (ceq : cfeqn) : eqn :=
  match ceq with
  | CEQExpr ce   => ExprEqn (ce_to_expr ce)
  | CEQEq v ce   => EqEqn v (ce_to_expr ce)
  end.

Fixpoint cxfill (CX : cx) (e : expr) : expr :=
  match CX with
  | CXHole         => e
  | CXEqR v CX' e' => (EqEqn v (cxfill CX' e)); e'
  | CXSeqL CX' e'  => (ExprEqn (cxfill CX' e)); e'
  | CXSeqR ceq CX' => (ceq_to_eqn ceq); (cxfill CX' e)
  | CXEx x CX'     => ExE x (cxfill CX' e)
  end.
