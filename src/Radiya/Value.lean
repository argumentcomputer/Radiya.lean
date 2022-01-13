import Radiya.Const
open Lean (Literal)

namespace Radiya

inductive Univ where
| zero
| succ : Univ → Univ
| max : Univ → Univ → Univ
| imax : Univ → Univ → Univ
| param : Nat → Univ

inductive Term where
| var   : Nat → Term
| sort  : Univ → Term
| const : Const → List Univ → Term
| app   : Term → Term → Term
| lam   : Term → Term → Term
| pi    : Term → Term → Term
| letE  : Term → Term → Term → Term
| lit   : Literal → Term
| fix   : Term → Term
deriving Inhabited

inductive ConstVal where
| axiomC   : Nat → Cid → ConstVal
| opaque   : Nat → Cid → ConstVal
| induct   : Nat → Nat → Nat → List Intro → Bool → ConstVal
| ctor     : Nat → ConstVal → Nat → Nat → Nat → Bool → ConstVal
| recursor : Nat → ConstVal → Nat → Nat → Nat → Nat → List RecRule → Bool → Bool → ConstVal
| quotType : Nat → ConstVal
| quotCtor : Nat → ConstVal
| quotLift : Nat → ConstVal
| quotInd  : Nat → ConstVal
deriving Inhabited

inductive Neutral where
| const : ConstVal → List Univ → Neutral
| var   : Nat → Neutral
deriving Inhabited

inductive Value where
| sort  : Univ → Value
| app   : Neutral → List (Thunk Value) → Value
| lam   : Term → List (Thunk Value) → Value
| pi    : Thunk Value → Term → List (Thunk Value) → Value
| lit   : Literal → Value
deriving Inhabited

def Env := List (Thunk Value)
def Args := List (Thunk Value)

instance : Inhabited (Thunk Value) where
  default := Thunk.mk (fun _ => Value.sort Univ.zero)

def mkVar (idx : Nat) : Value :=
  Value.app (Neutral.var idx) []

partial def eval (term : Term) (env : Env) : Value :=
  match term with
  | Term.app fnc arg =>
    let thunk := Thunk.mk (fun _ => eval arg env)
    match eval fnc env with
    | Value.lam bod lam_env => eval bod (thunk :: lam_env)
    | Value.app (Neutral.var idx) args => Value.app (Neutral.var idx) (thunk :: args)
    | Value.app (Neutral.const _ _) _ => panic! "TODO"
    -- Since terms are typed checked we know that any other case is impossible
    | _ => panic! "Impossible"
  | Term.lam _ bod => Value.lam bod env
  | Term.var idx =>
    let thunk := List.get! env idx
    thunk.get
  | Term.const _ _ => panic! "TODO"
  | Term.letE _ val bod =>
    let thunk := Thunk.mk (fun _ => eval val env)
    eval bod (thunk :: env)
  | Term.fix bod =>
    let thunk := Thunk.mk (fun _ => eval term env)
    eval bod (thunk :: env)
  | Term.pi dom img =>
    let dom := Thunk.mk (fun _ => eval dom env)
    Value.pi dom img env
  | Term.sort univ => Value.sort univ
  | Term.lit lit => Value.lit lit

def equal_univ (u u' : Univ) : Bool :=
  panic! "TODO"

def equal_univs (us us' : List Univ) : Bool :=
  match us, us' with
  | [], [] => true
  | u::us, u'::us' => equal_univ u u' && equal_univs us us'
  | _, _ => false

def equal_const (k k' : ConstVal) : Bool :=
  panic! "TODO"

def equal_neu (n n' : Neutral) : Bool :=
  match n, n' with
  | Neutral.var idx, Neutral.var idx' => idx == idx'
  | Neutral.const k us, Neutral.const k' us' =>
    equal_const k k' && equal_univs us us'
  | _, _ => false

mutual
  partial def equal (lvl : Nat) (term term' : Value) : Bool :=
    match term, term' with
    | Value.lit lit, Value.lit lit' => lit == lit'
    | Value.sort u, Value.sort u' => equal_univ u u'
    | Value.app neu args, Value.app neu' args' => equal_neu neu neu' && equal_thunks lvl args args'
    | Value.pi dom img env, Value.pi dom' img' env' =>
      let var := mkVar lvl
      equal lvl dom.get dom'.get &&
      equal (lvl + 1) (eval img (var :: env)) (eval img' (var :: env'))
    | Value.lam bod env, Value.lam bod' env' =>
      let var := mkVar lvl
      equal (lvl + 1) (eval bod (var :: env)) (eval bod' (var :: env'))
    | Value.lam bod env, Value.app neu' args' =>
      let var := mkVar lvl
      equal (lvl + 1) (eval bod (var :: env)) (Value.app neu' (var :: args'))
    | Value.app neu args, Value.lam bod' env' =>
      let var := mkVar lvl
      equal (lvl + 1) (Value.app neu (var :: args)) (eval bod' (var :: env'))
    | _, _ => false

  partial def equal_thunks (lvl : Nat) (vals vals' : List (Thunk Value)) : Bool :=
    match vals, vals' with
    | [], [] => true
    | val::vals, val'::vals' => equal lvl val.get val'.get && equal_thunks lvl vals vals'
    | _, _ => false
end

inductive CheckError (A : Type) where
| ok : A → CheckError A
| notPi : CheckError A
| notTyp : CheckError A
| notSameValues : CheckError A
deriving Inhabited

structure Ctx where
  lvl   : Nat
  env   : Env
  types : List (Thunk Value)

def extCtx (ctx : Ctx) (val : Thunk Value) (typ : Thunk Value) : Ctx :=
  Ctx.mk (ctx.lvl + 1) (val :: ctx.env) (typ :: ctx.types)

instance : Monad CheckError where
  pure x := CheckError.ok x
  bind x f := match x with
  | CheckError.ok y => f y
  | CheckError.notPi => CheckError.notPi
  | CheckError.notTyp => CheckError.notTyp
  | CheckError.notSameValues => CheckError.notSameValues
  map f x := match x with
  | CheckError.ok y => CheckError.ok (f y)
  | CheckError.notPi => CheckError.notPi
  | CheckError.notTyp => CheckError.notTyp
  | CheckError.notSameValues => CheckError.notSameValues

mutual
  partial def check (ctx : Ctx) (term : Term) (type : Value) : CheckError Unit :=
    match term, type with
    | Term.lam lam_dom bod, Value.pi dom img env =>
      -- TODO check that `lam_dom` == `dom`
      -- though this is wasteful, since this would force
      -- `dom`, which might not need to be evaluated.
      let var := mkVar ctx.lvl
      let ctx := extCtx ctx var dom
      check ctx bod (eval img (var :: env))
    | Term.lam _ _, _ =>
      CheckError.notPi
    | Term.letE typ exp bod, let_typ => do
      let sort ← infer ctx typ
      match sort with
      | Value.sort u => pure ()
      | _ => CheckError.notTyp
      let typ := eval typ ctx.env
      check ctx exp typ
      let exp := Thunk.mk (fun _ => eval exp ctx.env)
      let typ := Thunk.mk (fun _ => typ)
      let ctx := extCtx ctx exp typ
      check ctx bod let_typ
    | term, type => do
      let infer_type ← infer ctx term
      if equal ctx.lvl type infer_type
      then CheckError.ok ()
      else CheckError.notSameValues
  partial def infer (ctx : Ctx) (term : Term) : CheckError Value :=
    panic! "TODO"
end
