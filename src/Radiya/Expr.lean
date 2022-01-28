import Radiya.Ipld.Cid
import Radiya.Univ

import Lean.Declaration
open Lean (Literal)

namespace Radiya

abbrev Name := String

inductive DefinitionSafety where
  | safe
  | unsa
  | part
  deriving Inhabited, BEq

inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
  deriving Inhabited, BEq

-- Lean does not support mutual blocks with structure and inductive, so we have to parametrize
-- the following structure
structure AxiomC (Expr : Type) where
  cid : Cid
  level : Nat
  type : Expr

structure TheoremC (Expr : Type) where
  level : Nat
  expr : Expr
  type : Expr

structure OpaqueC (Expr : Type) where
  cid : Cid
  level : Nat
  expr : Expr
  type : Expr
  is_unsafe : Bool

structure DefinitionC (Expr : Type) where
  cid : Cid
  level : Nat
  expr : Expr
  type : Expr
  safety : DefinitionSafety

structure ConstructorC (Expr : Type) where
  cid : Cid
  level : Nat
  type : Expr
  ctor_idx : Nat
  num_params : Nat
  num_fields : Nat
  is_unsafe : Bool

structure InductiveC (Expr : Type) where
  cid : Cid
  level : Nat
  type : Expr
  num_params : Nat
  num_indices : Nat
  ctors : List (ConstructorC Expr)
  is_rec : Bool
  is_unsafe : Bool
  is_reflexive : Bool
  is_nested : Bool

structure RecursorRule (Expr : Type) where
  ctor : Name
  nfields : Nat
  rhs : Expr

structure RecursorC (Expr : Type) where
  cid : Cid
  level : Nat
  type : Expr
  num_params : Nat
  num_indices : Nat
  num_motives : Nat
  num_minors : Nat
  rules : List (RecursorRule Expr)
  k : Bool
  is_unsafe : Bool

structure QuotientC (Expr : Type) where
  level : Nat
  type : Expr
  kind : QuotKind

mutual
  inductive Const where
  | axiomC   : AxiomC Expr → Const
  | theoremC : TheoremC Expr → Const
  | opaque   : OpaqueC Expr → Const
  | defn     : DefinitionC Expr → Const
  | induct   : InductiveC Expr → Const
  | ctor     : ConstructorC Expr → Const
  | recursor : RecursorC Expr → Const
  | quotient : QuotientC Expr → Const

  inductive Expr where
  | var   : Nat → Expr
  | sort  : Univ → Expr
  | const : Const → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Expr → Expr → Expr
  | pi    : Expr → Expr → Expr
  | letE  : Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | fix   : Expr → Expr
  deriving Inhabited
end

def extractConstType (k : Const) : Expr :=
  match k with
  | Const.axiomC x => x.type
  | Const.theoremC x => x.type
  | Const.opaque x => x.type
  | Const.defn x => x.type
  | Const.induct x => x.type
  | Const.ctor x => x.type
  | Const.recursor x => x.type
  | Const.quotient x => x.type

end Radiya
