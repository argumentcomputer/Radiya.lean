import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor
import Radiya.ToIpld

import Lean.Declaration

open Lean (QuotKind DefinitionSafety)

namespace Radiya

structure RecRule where
  ctor : NameCid
  fields : Nat
  rhs : ExprCid

structure Intro where
  ctor : NameCid
  typ : ExprCid

inductive Const where
| quotient : Nat → ExprCid → QuotKind → Const
| axiomC   : Nat → ExprCid → Bool → Cid → Const
| theoremC : Nat → ExprCid → ExprCid → Const
| opaque   : Nat → ExprCid → ExprCid → Bool → Cid → Const
| defC     : Nat → ExprCid → ExprCid → Bool → DefinitionSafety → Const
| induct   : Nat → ExprCid → Nat → Nat → List Intro → Bool → Const
| ctor     : Nat → ExprCid → ConstCid → Nat → Nat → Nat → Bool → Const
| recursor : Nat → ExprCid → ConstCid → Nat → Nat → Nat → Nat → List RecRule → Bool → Bool → Const

inductive ConstMeta where
| quotient : NameCid → List NameCid → ExprCid → ConstMeta
| axiomC   : NameCid → List NameCid → ExprCid → ConstMeta
| theoremC : NameCid → List NameCid → ExprCid → ExprCid → ConstMeta
| opaque   : NameCid → List NameCid → ExprCid → ExprCid → ConstMeta
| defC     : NameCid → List NameCid → ExprCid → ExprCid → ConstMeta
| induct   : NameCid → List NameCid → ExprCid → List ExprMetaCid → ConstMeta
| ctor     : NameCid → List NameCid → ExprCid → ConstMetaCid → ConstMeta
| recursor : NameCid → List NameCid → ExprCid → List ExprMetaCid → ConstMeta


end Radiya
