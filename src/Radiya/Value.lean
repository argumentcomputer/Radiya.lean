import Radiya.Ipld.Cid
import Radiya.Univ
import Radiya.Expr

open Lean (Literal QuotKind)

namespace Radiya

inductive ConstVal where
| axiomC   : Nat → Cid → ConstVal
| opaque   : Nat → Cid → ConstVal
| induct   : Nat → Nat → Nat → List (Intro Expr) → Bool → ConstVal
| ctor     : Nat → Const → Nat → Nat → Nat → Bool → ConstVal
| recursor : Nat → Const → Nat → Nat → Nat → Nat → List (RecRule Expr) → Bool → Bool → ConstVal
| quotient : Nat → QuotKind → ConstVal
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
    | Const.quotient size _ kind => mkConst (ConstVal.quotient size kind) univs
    | Const.axiomC   size _ _ cid => mkConst (ConstVal.axiomC size cid) univs
    | Const.theoremC size _ exp => eval exp [] univs
    | Const.opaque   size _ _ _ cid => mkConst (ConstVal.opaque size cid) univs
    | Const.defn     size _ exp _ => eval exp [] univs
    | Const.induct   size _ params indices intros isUnsafe =>
      mkConst (ConstVal.induct size params indices intros isUnsafe) univs
    | Const.ctor     size _ induct cidx params fields isUnsafe =>
      mkConst (ConstVal.ctor size induct cidx params fields isUnsafe) univs
    | Const.recursor size _ induct indices params motives minors recRules isK isUnsafe =>
      mkConst (ConstVal.recursor size induct indices params motives minors recRules isK isUnsafe) univs

  partial def eval (term : Expr) (env : Env) (univs : List Univ) : Value :=
    match term with
    | Expr.app fnc arg =>
      let thunk := Thunk.mk (fun _ => eval arg env univs)
      match eval fnc env univs with
      | Value.lam bod lam_env lam_univs => eval bod (thunk :: lam_env) lam_univs
      | Value.app (Neutral.var idx) args => Value.app (Neutral.var idx) (thunk :: args)
      | Value.app (Neutral.const _ _) _ => panic! "TODO"
      -- Since terms are typed checked we know that any other case is impossible
      | _ => panic! "Impossible"
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

def quote (lvl : Nat) (val : Value) : Expr :=
  panic! "TODO"

def equalConst (k k' : ConstVal) : Bool :=
  panic! "TODO"

def equalNeu (n n' : Neutral) : Bool :=
  match n, n' with
  | Neutral.var idx, Neutral.var idx' => idx == idx'
  | Neutral.const k us, Neutral.const k' us' =>
    equalConst k k' && equalUnivs us us'
  | _, _ => false

mutual
  partial def equal (lvl : Nat) (term term' : Value) : Bool :=
    match term, term' with
    | Value.lit lit, Value.lit lit' => lit == lit'
    | Value.sort u, Value.sort u' => equalUniv u u'
    | Value.app neu args, Value.app neu' args' => equalNeu neu neu' && equalThunks lvl args args'
    | Value.pi dom img env univs, Value.pi dom' img' env' univs' =>
      let var := mkVar lvl
      equal lvl dom.get dom'.get &&
      equal (lvl + 1) (eval img (var :: env) univs) (eval img' (var :: env') univs')
    | Value.lam bod env univs, Value.lam bod' env' univs' =>
      let var := mkVar lvl
      equal (lvl + 1) (eval bod (var :: env) univs) (eval bod' (var :: env') univs')
    | Value.lam bod env univs, Value.app neu' args' =>
      let var := mkVar lvl
      equal (lvl + 1) (eval bod (var :: env) univs) (Value.app neu' (var :: args'))
    | Value.app neu args, Value.lam bod' env' univs' =>
      let var := mkVar lvl
      equal (lvl + 1) (Value.app neu (var :: args)) (eval bod' (var :: env') univs')
    | _, _ => false

  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value)) : Bool :=
    match vals, vals' with
    | [], [] => true
    | val::vals, val'::vals' => equal lvl val.get val'.get && equalThunks lvl vals vals'
    | _, _ => false
end

inductive CheckError (A : Type) where
| ok : A → CheckError A
| notPi : CheckError A
| notTyp : CheckError A
| notSameValues : CheckError A
| cannotInferFix : CheckError A
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
  map f x := match x with
  | CheckError.ok y => CheckError.ok (f y)
  | CheckError.notPi => CheckError.notPi
  | CheckError.notTyp => CheckError.notTyp
  | CheckError.notSameValues => CheckError.notSameValues
  | CheckError.cannotInferFix => CheckError.cannotInferFix

mutual
  partial def check (ctx : Ctx) (term : Expr) (type : Value) : CheckError Unit :=
    match term, type with
    | Expr.lam lam_dom bod, Value.pi dom img env pi_univs =>
      -- TODO check that `lam_dom` == `dom`
      -- though this is wasteful, since this would force
      -- `dom`, which might not need to be evaluated.
      let var := mkVar ctx.lvl
      let ctx := extCtx ctx var dom
      check ctx bod (eval img (var :: env) pi_univs)
    | Expr.lam _ _, _ =>
      CheckError.notPi
    | Expr.letE typ exp bod, let_typ => do
      let sort ← infer ctx typ
      match sort with
      | Value.sort u => pure ()
      | _ => CheckError.notTyp
      let typ := eval typ ctx.env ctx.univs
      check ctx exp typ
      let exp := Thunk.mk (fun _ => eval exp ctx.env ctx.univs)
      let typ := Thunk.mk (fun _ => typ)
      let ctx := extCtx ctx exp typ
      check ctx bod let_typ
    | Expr.fix bod, type =>
      let ctx := extCtx ctx (Thunk.mk (fun _ => eval term ctx.env ctx.univs)) type
      check ctx bod type
    | term, type => do
      let infer_type ← infer ctx term
      if equal ctx.lvl type infer_type
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
    | Expr.lam dom bod => do
      match infer ctx dom with
        | Value.sort u => pure ()
        | _ => CheckError.notTyp
      let dom := Thunk.mk (fun _ => eval dom ctx.env ctx.univs)
      let ctx := extCtx ctx (mkVar ctx.lvl) dom
      let bod_type ← infer ctx bod
      let img := quote ctx.lvl bod_type
      Value.pi dom img ctx.env ctx.univs
    | Expr.pi dom img  => do
      let dom_lvl ← match infer ctx dom with
        | Value.sort u => pure u
        | _ => CheckError.notTyp
      let ctx := extCtx ctx (mkVar ctx.lvl) (Thunk.mk (fun _ => eval dom ctx.env ctx.univs))
      let img_lvl ← match infer ctx img with
        | Value.sort u => pure u
        | _ => CheckError.notTyp
      pure (Value.sort (Univ.imax dom_lvl img_lvl))
    | Expr.letE typ exp bod => do
      let sort ← infer ctx typ
      match sort with
      | Value.sort u => pure ()
      | _ => CheckError.notTyp
      let typ := eval typ ctx.env ctx.univs
      check ctx exp typ
      let exp := Thunk.mk (fun _ => eval exp ctx.env ctx.univs)
      let typ := Thunk.mk (fun _ => typ)
      let ctx := extCtx ctx exp typ
      infer ctx bod
    | Expr.fix _ =>
      CheckError.cannotInferFix
    | Expr.lit _ => panic! "TODO"
    | Expr.const _ _ => panic! "TODO"
end

end Radiya
