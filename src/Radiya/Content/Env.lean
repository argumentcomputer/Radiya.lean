import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor
import Radiya.ToIpld
import Radiya.Cid
import Radiya.Name
import Radiya.Univ
import Radiya.Expr

import Lean
import Lean.Expr

import Std.Data.RBTree

open Lean (Literal)

open Std (RBNode)

namespace Radiya

structure Env where
  lit : RBNode LitCid (fun _ => Literal)
  name : RBNode NameCid (fun _ => Name)
  univ : RBNode UnivCid (fun _ => Univ)
  univMeta : RBNode UnivMetaCid (fun _ => UnivMeta)
  expr : RBNode ExprCid (fun _ => Expr)
  exprMeta : RBNode ExprMetaCid (fun _ => ExprMeta)
  const : RBNode ExprCid (fun _ => Expr)
  constMeta : RBNode ExprMetaCid (fun _ => ExprMeta)

end Radiya
