import Radiya.Ipld.Cid
import Radiya.Univ
import Radiya.Expr

open Lean (Literal QuotKind)

namespace Radiya

inductive ConstVal where
| axiomC   : Cid → Nat → ConstVal
| opaque   : Cid → Nat → ConstVal
| induct   : Cid → Nat → Nat → Nat → List (Intro Expr) → Bool → ConstVal
| ctor     : Cid → Nat → Const → Nat → Nat → Nat → Bool → ConstVal
| recursor : Cid → Nat → Const → Nat → Nat → Nat → Nat → List (RecRule Expr) → Bool → Bool → ConstVal
| quotient : Cid → Nat → QuotKind → ConstVal
deriving Inhabited

inductive Neutral where
| const : ConstVal → List Univ → Neutral
| var   : Nat → Neutral
deriving Inhabited

inductive Value where
| sort  : Univ → Value
| app   : Neutral → List (Thunk Value) → Value
| lam   : Expr → List (Thunk Value) → List Univ → Value
| pi    : Thunk Value → Expr → List (Thunk Value) → List Univ → Value
| lit   : Literal → Value
deriving Inhabited

def Env := List (Thunk Value)
def Args := List (Thunk Value)

instance : Inhabited (Thunk Value) where
  default := Thunk.mk (fun _ => Value.sort Univ.zero)

def mkConst (k : ConstVal) (univs : List Univ) : Value :=
  Value.app (Neutral.const k univs) []

def mkVar (idx : Nat) : Value :=
  Value.app (Neutral.var idx) []

mutual
  partial def evalConst (const : Const) (univs : List Univ) : Value :=
    match const with
    | Const.quotient cid size _ kind => mkConst (ConstVal.quotient cid size kind) univs
    | Const.axiomC   cid size _ _ => mkConst (ConstVal.axiomC cid size) univs
    | Const.theoremC cid size _ exp => eval exp [] univs
    | Const.opaque   cid size _ _ _ => mkConst (ConstVal.opaque cid size) univs
    | Const.defn     cid size _ exp _ => eval exp [] univs
    | Const.induct   cid size _ params indices intros isUnsafe =>
      mkConst (ConstVal.induct cid size params indices intros isUnsafe) univs
    | Const.ctor     cid size _ induct cidx params fields isUnsafe =>
      mkConst (ConstVal.ctor cid size induct cidx params fields isUnsafe) univs
    | Const.recursor cid size _ induct indices params motives minors recRules isK isUnsafe =>
      mkConst (ConstVal.recursor cid size induct indices params motives minors recRules isK isUnsafe) univs

  partial def eval (term : Expr) (env : Env) (univs : List Univ) : Value :=
    match term with
    | Expr.app fnc arg =>
      let thunk := Thunk.mk (fun _ => eval arg env univs)
      match eval fnc env univs with
      | Value.lam bod lam_env lam_univs => eval bod (thunk :: lam_env) lam_univs
      | Value.app var@(Neutral.var _) args => Value.app var (thunk :: args)
      | Value.app (Neutral.const _ _) _ => panic! "TODO"
      -- Since terms are typed checked we know that any other case is impossible
      | _ => panic! "Impossible eval case"
    | Expr.lam _ bod => Value.lam bod env univs
    | Expr.var idx =>
      let thunk := List.get! env idx
      thunk.get
    | Expr.const k const_univs => evalConst k (List.map (instantiateBulk univs) const_univs)
    | Expr.letE _ val bod =>
      let thunk := Thunk.mk (fun _ => eval val env univs)
      eval bod (thunk :: env) univs
    | Expr.fix bod =>
      let thunk := Thunk.mk (fun _ => eval term env univs)
      eval bod (thunk :: env) univs
    | Expr.pi dom img =>
      let dom := Thunk.mk (fun _ => eval dom env univs)
      Value.pi dom img env univs
    | Expr.sort univ => Value.sort (instantiateBulk univs univ)
    | Expr.lit lit => Value.lit lit
end

def equalConst (k k' : ConstVal) : Bool :=
  match k, k' with
-- It is assumed here that equal CIDs imply equal sizes of parameters bound.
-- This is a fair assumption since the elaborator should never build constants
-- of same kind and CIDs but different binding sizes.
| ConstVal.induct cid _ _ _ _ _, ConstVal.induct cid' _ _ _ _ _ => cid == cid'
| ConstVal.ctor cid _ _ _ _ _ _, ConstVal.ctor cid' _ _ _ _ _ _ => cid == cid'
| ConstVal.recursor cid _ _ _ _ _ _ _ _ _, ConstVal.recursor cid' _ _ _ _ _ _ _ _ _ => cid == cid'
| ConstVal.quotient cid _ QuotKind.ctor, ConstVal.quotient cid' _ QuotKind.ctor => cid == cid'
| ConstVal.quotient cid _ QuotKind.type, ConstVal.quotient cid' _ QuotKind.type => cid == cid'
| ConstVal.quotient cid _ QuotKind.ind, ConstVal.quotient cid' _ QuotKind.ind => cid == cid'
| ConstVal.quotient cid _ QuotKind.lift, ConstVal.quotient cid' _ QuotKind.lift => cid == cid'
-- By not carrying the types, we assume the CIDs of axiom values and opaque values will differ by name and type.
-- This means that axioms are only equal if their names are equal and their types are *syntactically* equal.
-- Otherwise, we could carry around the types and checking here for beta-eta convertibility (a more general kind
-- of equality) and have CIDs only differ by name.
| ConstVal.axiomC cid _, ConstVal.axiomC cid' _ => cid == cid'
| ConstVal.opaque cid _, ConstVal.opaque cid' _ => cid == cid'
| _, _ => false

def equalNeu (n n' : Neutral) : Bool :=
  match n, n' with
  | Neutral.var idx, Neutral.var idx' => idx == idx'
  | Neutral.const k us, Neutral.const k' us' =>
    equalConst k k' && equalUnivs us us'
  | _, _ => false

def isUnit (lvl : Nat) (term : Value) : Bool :=
  false -- TODO

def isProp (lvl : Nat) (term : Value) : Bool :=
  false -- TODO

mutual
  -- It is assumed here that the terms are typechecked, have both the same type
  -- and live in the same environment
  partial def equal (lvl : Nat) (term term' type : Value) : Bool :=
    if isUnit lvl type || isProp lvl type then true
    else match term, term' with
    | Value.lit lit, Value.lit lit' => lit == lit'
    | Value.sort u, Value.sort u' => equalUniv u u'
    | Value.pi dom img env univs, Value.pi dom' img' env' univs' =>
      let var := mkVar lvl
      -- For equality we don't need to know the universe levels, only the "shape" of the type.
      -- If we did have to know the universe level, then we probably would have to cache it
      -- so that we wouldn't need to infer the type just to get the level.
      -- Here, it is assumed that `type` is some a `Sort`
      equal lvl dom.get dom'.get type &&
      equal (lvl + 1) (eval img (var :: env) univs) (eval img' (var :: env') univs') type
    | Value.lam bod env univs, Value.lam bod' env' univs' =>
      match type with
      | Value.pi _ img pi_env pi_univs =>
        let var := mkVar lvl
        let bod := eval bod (var :: env) univs
        let bod' := eval bod' (var :: env') univs'
        let img := eval img (var :: pi_env) pi_univs
        equal (lvl + 1) bod bod' img
      | _ => panic! "Impossible equal case"
    | Value.lam bod env univs, Value.app neu' args' =>
      match type with
      | Value.pi _ img pi_env pi_univs =>
        let var := mkVar lvl
        let bod := eval bod (var :: env) univs
        let app := Value.app neu' (var :: args')
        let img := eval img (var :: pi_env) pi_univs
        equal (lvl + 1) bod app img
      | _ => panic! "Impossible equal case"
    | Value.app neu args, Value.lam bod' env' univs' =>
      match type with
      | Value.pi _ img pi_env pi_univs =>
        let var := mkVar lvl
        let bod := eval bod' (var :: env') univs'
        let app := Value.app neu (var :: args)
        let img := eval img (var :: pi_env) pi_univs
        equal (lvl + 1) app bod img
      | _ => panic! "Impossible equal case"
    | Value.app neu args, Value.app neu' args' => equalNeu neu neu' && equalThunks lvl args args' type -- TODO
    | _, _ => false

  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value)) (type : Value) : Bool :=
    match vals, vals' with
    | [], [] => true
    | val::vals, val'::vals' => equal lvl val.get val'.get type && equalThunks lvl vals vals' type -- TODO
    | _, _ => false
end

inductive CheckError (A : Type) where
| ok : A → CheckError A
| notPi : CheckError A
| notTyp : CheckError A
| notSameValues : CheckError A
| cannotInferFix : CheckError A
| cannotInferLam : CheckError A
deriving Inhabited

structure Ctx where
  lvl   : Nat
  env   : Env
  types : List (Thunk Value)
  univs : List Univ

def extCtx (ctx : Ctx) (val : Thunk Value) (typ : Thunk Value) : Ctx :=
  Ctx.mk (ctx.lvl + 1) (val :: ctx.env) (typ :: ctx.types) ctx.univs

instance : Monad CheckError where
  pure x := CheckError.ok x
  bind x f := match x with
  | CheckError.ok y => f y
  | CheckError.notPi => CheckError.notPi
  | CheckError.notTyp => CheckError.notTyp
  | CheckError.notSameValues => CheckError.notSameValues
  | CheckError.cannotInferFix => CheckError.cannotInferFix
  | CheckError.cannotInferLam => CheckError.cannotInferLam
  map f x := match x with
  | CheckError.ok y => CheckError.ok (f y)
  | CheckError.notPi => CheckError.notPi
  | CheckError.notTyp => CheckError.notTyp
  | CheckError.notSameValues => CheckError.notSameValues
  | CheckError.cannotInferFix => CheckError.cannotInferFix
  | CheckError.cannotInferLam => CheckError.cannotInferLam

mutual
  partial def check (ctx : Ctx) (term : Expr) (type : Value) : CheckError Unit :=
    match term with
    | Expr.lam lam_dom bod =>
      match type with
      | Value.pi dom img env pi_univs =>
        -- TODO check that `lam_dom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        let var := mkVar ctx.lvl
        let ctx := extCtx ctx var dom
        check ctx bod (eval img (var :: env) pi_univs)
      | _ => CheckError.notPi
    | Expr.letE exp_typ exp bod => do
      let sort ← infer ctx exp_typ
      match sort with
      | Value.sort u => pure ()
      | _ => CheckError.notTyp
      let exp_typ := eval exp_typ ctx.env ctx.univs
      check ctx exp exp_typ
      let exp := Thunk.mk (fun _ => eval exp ctx.env ctx.univs)
      let exp_typ := Thunk.mk (fun _ => exp_typ)
      let ctx := extCtx ctx exp exp_typ
      check ctx bod type
    | Expr.fix bod =>
      let ctx := extCtx ctx (Thunk.mk (fun _ => eval term ctx.env ctx.univs)) type
      check ctx bod type
    | _ => do
      let infer_type ← infer ctx term
      if equal ctx.lvl type infer_type (Value.sort Univ.zero)
      then pure ()
      else CheckError.notSameValues

  partial def infer (ctx : Ctx) (term : Expr) : CheckError Value :=
    match term with
    | Expr.var idx =>
      let type := List.get! ctx.types idx
      pure type.get
    | Expr.sort lvl =>
      let type := Value.sort (Univ.succ lvl)
      pure type
    | Expr.app fnc arg => do
      let fnc_typ ← infer ctx fnc
      match fnc_typ with
      | Value.pi dom img env pi_univs => do
        check ctx arg dom.get
        let arg := Thunk.mk (fun _ => eval arg ctx.env ctx.univs)
        let type := eval img (arg :: env) pi_univs
        pure type
      | _ => CheckError.notPi
      -- Should we add inference of lambda terms? Perhaps not on this checker,
      -- but on another that is capable of general unification, since this checker
      -- is supposed to be used on fully annotated terms.
    | Expr.lam dom bod => CheckError.cannotInferLam
    | Expr.pi dom img  => do
      let dom_lvl ← match infer ctx dom with
        | Value.sort u => pure u
        | _ => CheckError.notTyp
      let ctx := extCtx ctx (mkVar ctx.lvl) (Thunk.mk (fun _ => eval dom ctx.env ctx.univs))
      let img_lvl ← match infer ctx img with
        | Value.sort u => pure u
        | _ => CheckError.notTyp
      pure (Value.sort (Univ.imax dom_lvl img_lvl))
    | Expr.letE exp_typ exp bod => do
      let sort ← infer ctx exp_typ
      match sort with
      | Value.sort u => pure ()
      | _ => CheckError.notTyp
      let exp_typ := eval exp_typ ctx.env ctx.univs
      check ctx exp exp_typ
      let exp := Thunk.mk (fun _ => eval exp ctx.env ctx.univs)
      let exp_typ := Thunk.mk (fun _ => exp_typ)
      let ctx := extCtx ctx exp exp_typ
      infer ctx bod
    | Expr.fix _ =>
      CheckError.cannotInferFix
    | Expr.lit _ => panic! "TODO"
    | Expr.const _ _ => panic! "TODO"
end

end Radiya
