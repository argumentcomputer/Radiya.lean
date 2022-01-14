import Radiya.Ipld.Cid
import Radiya.Univ

import Lean.Declaration
open Lean (Literal DefinitionSafety QuotKind)

namespace Radiya

def Name := String

-- Lean does not support mutual blocks with structure and inductive, so we have to parametrize
-- the following structures
structure RecRule (Expr : Type) where
  ctor : Name
  fields : Nat
  rhs : Expr

structure Intro (Expr : Type) where
  ctor : Name
  typ : Expr

mutual
  inductive Const where
  | quotient : Nat → Expr → QuotKind → Const
  | axiomC   : Nat → Expr → Bool → Cid → Const
  | theoremC : Nat → Expr → Expr → Const
  | opaque   : Nat → Expr → Expr → Bool → Cid → Const
  | defn     : Nat → Expr → Expr → DefinitionSafety → Const
  | induct   : Nat → Expr → Nat → Nat → List (Intro Expr) → Bool → Const
  | ctor     : Nat → Expr → Const → Nat → Nat → Nat → Bool → Const
  | recursor : Nat → Expr → Const → Nat → Nat → Nat → Nat → List (RecRule Expr) → Bool → Bool → Const

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

end Radiya
