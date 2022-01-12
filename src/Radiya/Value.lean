import Radiya.Univ
import Radiya.Const
open Lean (Literal)

namespace Radiya

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

mutual
  partial def eval (term : Term) (env : Env) (args : Args) : Value :=
    match term with
    | Term.app fnc arg =>
      let thunk := Thunk.mk (fun _ => eval arg env [])
      eval fnc env (thunk :: args)
    | Term.lam _ bod => match args with
      | [] => Value.lam bod env
      | arg :: args => eval bod (arg :: env) args
    | Term.var idx =>
      let thunk := List.get! env idx
      apply thunk.get args
    | Term.const _ _ => panic! "TODO"
    | Term.letE _ val bod =>
      let thunk := Thunk.mk (fun _ => eval val env [])
      eval bod (thunk :: env) args
    | Term.fix bod =>
      let thunk := Thunk.mk (fun _ => eval term env [])
      eval bod (thunk :: env) args
    -- Since terms are typed checked we know `args` must be empty for these last cases
    | Term.pi dom img =>
      let dom := Thunk.mk (fun _ => eval dom env [])
      Value.pi dom img env
    | Term.sort univ => Value.sort univ
    | Term.lit lit => Value.lit lit

  partial def apply (value : Value) (args : Args) : Value :=
    match args with
    | [] => value
    | arg :: args' => match value with
      | Value.lam bod env => eval bod (arg :: env) args'
      | Value.app neu args' => Value.app neu (List.append args' args)
      | _ => panic! "Impossible"
end

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
      let var := Value.app (Neutral.var lvl) []
      equal lvl dom.get dom'.get &&
      equal (lvl + 1) (eval img (var :: env) []) (eval img' (var :: env') [])
    | Value.lam bod env, Value.lam bod' env' =>
      let var := Value.app (Neutral.var lvl) []
      equal (lvl + 1) (eval bod (var :: env) []) (eval bod' (var :: env') [])
    | Value.lam bod env, Value.app neu' args' => panic! "TODO"
    | Value.app neu' args', Value.lam bod' env' => panic! "TODO"
    | _, _ => false

  partial def equal_thunks (lvl : Nat) (vals vals' : List (Thunk Value)) : Bool :=
    match vals, vals' with
    | [], [] => true
    | val::vals, val'::vals' => equal lvl val.get val'.get && equal_thunks lvl vals vals'
    | _, _ => false
end
