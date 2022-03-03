import Radiya.Ipld.Cid
import Radiya.Univ
import Radiya.Expr

namespace Radiya

mutual
  inductive Value where
  | sort  : Univ → Value
  | app   : Neutral → List (Thunk Value) → Value
  | lam   : Expr → List (Thunk Value) → List Univ → Value
  | pi    : Thunk Value → Expr → List (Thunk Value) → List Univ → Value
  | lit   : Literal → Value
  | lty   : LitType → Value

  -- Here variables also carry their types, but this is purely for an optimization
  -- in equal, so that it doesn't need to carry around a context of types
  inductive Neutral where
  | const : Const → List Univ → Neutral
  | var   : Nat → Thunk Value → Neutral
end

-- Had to manually define inhabited instances because Lean could not automatically derive them
instance : Inhabited Value where
  default := Value.sort Univ.zero

instance : Inhabited Neutral where
  default := Neutral.var 0 (Thunk.mk (fun _ => Value.sort Univ.zero))

abbrev Env := List (Thunk Value)
abbrev Args := List (Thunk Value)

instance : Inhabited (Thunk Value) where
  default := Thunk.mk (fun _ => Value.sort Univ.zero)

def mkConst (k : Const) (univs : List Univ) : Value :=
  Value.app (Neutral.const k univs) []

def mkVar (idx : Nat) (type : Thunk Value) : Value :=
  Value.app (Neutral.var idx type) []

mutual
  partial def evalConst (const : Const) (univs : List Univ) : Value :=
    match const with
    | Const.theoremC x =>
      eval x.expr [] univs
    | Const.defn x =>
      match x.safety with
      | DefinitionSafety.safe => eval x.expr [] univs
      | DefinitionSafety.part => mkConst const univs
      | DefinitionSafety.unsa => panic! "Unsafe definition found"
    | _ => mkConst const univs

  partial def applyConst (k : Const) (univs : List Univ) (arg : Thunk Value) (args : List (Thunk Value)) : Value :=
  -- Assumes a partial application of k to args, which means in particular, that it is in normal form
    match k with
    | Const.recursor recur =>
      let major_idx := recur.num_params + recur.num_motives + recur.num_minors + recur.num_indices
      if args.length != major_idx then Value.app (Neutral.const k univs) (arg :: args)
      else
        match arg.get with
        | Value.app (Neutral.const (Const.ctor ctor) _) args' =>
          -- Since we assume expressions are previously type checked, we know that this constructor
          -- must have an associated recursion rule
          let rule := Option.get! (List.find? (fun r => r.ctor == ctor.cid) recur.rules)
          let env := List.append (List.take rule.nfields args') (List.drop recur.num_indices args)
          eval rule.rhs env univs
        | _ => Value.app (Neutral.const k univs) (arg :: args)
    | _ => Value.app (Neutral.const k univs) (arg :: args)

  partial def eval (term : Expr) (env : Env) (univs : List Univ) : Value :=
    match term with
    | Expr.app fnc arg =>
      let arg_thunk := Thunk.mk (fun _ => eval arg env univs)
      match eval fnc env univs with
      | Value.lam bod lam_env lam_univs => eval bod (arg_thunk :: lam_env) lam_univs
      | Value.app var@(Neutral.var ..) args => Value.app var (arg_thunk :: args)
      | Value.app (Neutral.const k k_univs) args => applyConst k k_univs arg_thunk args
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
    | Expr.lty lty => Value.lty lty
end

-- Assumes evaluated (delta-reduced) constants
def equalConst (k k' : Const) : Bool :=
  match k, k' with
  | Const.induct x, Const.induct x' => x.cid == x'.cid
  | Const.ctor x, Const.ctor x' => x.cid == x'.cid && x.ctor_idx == x'.ctor_idx
  | Const.recursor x, Const.recursor x' => x.cid == x'.cid
  | Const.quotient x, Const.quotient x' => x.kind == x'.kind
  -- We assume the CIDs of axiom values and opaque values will differ by name and type. This means
  -- that axioms are only equal if their names are equal and their types are *syntactically* equal.
  -- Otherwise, we could check the types for beta-eta convertibility, a more general kind of equality,
  -- and have CIDs only differ by name.
  | Const.axiomC x, Const.axiomC x' => x.cid == x'.cid
  | Const.opaque x, Const.opaque x' => x.cid == x'.cid
  | Const.defn x, Const.defn x' => x.cid == x'.cid
  | _, _ => false

def isUnit (lvl : Nat) (type : Value) : Bool :=
  match type with
  | Value.app (Neutral.const (Const.induct induct) ..) _ =>
    match induct.ctors with
    | [ctor] => ctor.num_fields == 0
    | _ => false
  | _ => false

def isProp (lvl : Nat) (type : Value) : Bool :=
  false -- TODO

mutual
  -- It is assumed here that the values are typechecked, have both the same type
  -- and their original unevaluated terms both lived in the same environment
  partial def equal (lvl : Nat) (term term' type : Value) : Bool :=
    if isUnit lvl type || isProp lvl type then true else
    match term, term' with
    | Value.lit lit, Value.lit lit' => lit == lit'
    | Value.lty lty, Value.lty lty' => lty == lty'
    | Value.sort u, Value.sort u' => equalUniv u u'
    | Value.pi dom img env univs, Value.pi dom' img' env' univs' =>
      let var := mkVar lvl dom
      -- For equality we don't need to know the universe levels, only the "shape" of the type.
      -- If we did have to know the universe level, then we probably would have to cache it
      -- so that we wouldn't need to infer the type just to get the level.
      -- Here, it is assumed that `type` is some a `Sort`
      equal lvl dom.get dom'.get type &&
      equal (lvl + 1) (eval img (var :: env) univs) (eval img' (var :: env') univs') type
    | Value.lam bod env univs, Value.lam bod' env' univs' =>
      match type with
      | Value.pi dom img pi_env pi_univs =>
        let var := mkVar lvl dom
        let bod := eval bod (var :: env) univs
        let bod' := eval bod' (var :: env') univs'
        let img := eval img (var :: pi_env) pi_univs
        equal (lvl + 1) bod bod' img
      | _ => panic! "Impossible equal case"
    | Value.lam bod env univs, Value.app neu' args' =>
      match type with
      | Value.pi dom img pi_env pi_univs =>
        let var := mkVar lvl dom
        let bod := eval bod (var :: env) univs
        let app := Value.app neu' (var :: args')
        let img := eval img (var :: pi_env) pi_univs
        equal (lvl + 1) bod app img
      | _ => panic! "Impossible equal case"
    | Value.app neu args, Value.lam bod' env' univs' =>
      match type with
      | Value.pi dom img pi_env pi_univs =>
        let var := mkVar lvl dom
        let bod := eval bod' (var :: env') univs'
        let app := Value.app neu (var :: args)
        let img := eval img (var :: pi_env) pi_univs
        equal (lvl + 1) app bod img
      | _ => panic! "Impossible equal case"
    | Value.app (Neutral.var idx var_type) args, Value.app (Neutral.var idx' _) args' =>
      -- If our assumption is correct, i.e., that these values come from terms in the same environment
      -- then their types are equal when their indices are equal
      idx == idx' &&
      List.length args == List.length args' &&
      equalThunks lvl args args' var_type
    | Value.app (Neutral.const k us) args, Value.app (Neutral.const k' us') args' =>
      -- Analogous assumption on the types of the constants
      let const_type := Thunk.mk (fun _ => eval (extractConstType k) [] us)
      equalConst k k' &&
      List.length args != List.length args' &&
      equalUnivs us us' &&
      equalThunks lvl args args' const_type
    | _, _ => false

  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value)) (type : Thunk Value) : Bool :=
    match vals, vals' with
    | val::vals, val'::vals' =>
      match type.get with
      | Value.pi dom img pi_env pi_univs =>
        let var := mkVar lvl dom
        let img := Thunk.mk (fun _ => eval img (var :: pi_env) pi_univs)
        equal lvl val.get val'.get dom.get && equalThunks lvl vals vals' img
      | _ => panic! "Impossible equal case"
    | [], [] => true
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
        let var := mkVar ctx.lvl dom
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
      let dom := Thunk.mk (fun _ => eval dom ctx.env ctx.univs)
      let ctx := extCtx ctx (mkVar ctx.lvl dom) dom
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
    | Expr.lit (Literal.natVal _) => Value.lty LitType.natTyp
    | Expr.lit (Literal.strVal _) => Value.lty LitType.strTyp
    | Expr.lty _ => Value.sort (Univ.succ Univ.zero)
    | Expr.const k const_univs => eval (extractConstType k) [] (List.map (instantiateBulk ctx.univs) const_univs)
end

end Radiya
