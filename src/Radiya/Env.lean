import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor
import Radiya.ToIpld
import Radiya.Cid
import Radiya.Name
import Radiya.Univ
import Radiya.Expr
import Radiya.Const

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
  env : RBNode ConstMetaCid (fun _ => ConstCid)

open ToIpld

def toIpldObject {α β: Type} [ToString α] [ToIpld β] (x : RBNode α (fun _ => β)): Ipld := Id.run do
  let xs := RBNode.toList x
  let mut map := RBNode.leaf
  for (k,v) in xs do
    map := map.insert compare (toString k) (toIpld v)
  return Ipld.object map

def fromIpldObject {α β : Type} [Ord α] [ToIpld β]
  (f: String -> Option α)
  (x : RBNode String (fun _ => Ipld))
  : Except IpldError (RBNode α (fun _ => β))
  := do
  let xs := RBNode.toList x
  let mut map := RBNode.leaf
  for (k, v) in xs do
    let k <- match f k with
      | Option.some x => pure x
      | Option.none => throw (IpldError.Expected "Valid String Key")
    let v <- fromIpld v
    map := map.insert compare k v
  return map

instance : ToIpld (RBNode LitCid (fun _ => Literal)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => LitCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode NameCid (fun _ => Name)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => NameCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode UnivCid (fun _ => Univ)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => UnivCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode UnivMetaCid (fun _ => UnivMeta)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => UnivMetaCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode ExprCid (fun _ => Expr)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => ExprCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode ExprMetaCid (fun _ => ExprMeta)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => ExprMetaCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode ConstCid (fun _ => Const)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => ConstCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode ConstMetaCid (fun _ => ConstMeta)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => ConstMetaCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld (RBNode ConstMetaCid (fun _ => ConstCid)) where
  toIpld xs := toIpldObject xs
  fromIpld
  | Ipld.object xs => fromIpldObject (fun x => ConstMetaCid.mk <$> (Cid.fromString x)) xs
  | other => throw (IpldError.Expected "Object")

instance : ToIpld Env where
  toIpld e := Ipld.array 
    #[ Ipld.number ENV, toIpld e.lit, toIpld e.name
     , toIpld e.univ, toIpld e.univMeta
     , toIpld e.expr, toIpld e.exprMeta
     , toIpld e.const, toIpld e.constMeta
     , toIpld e.env
     ]
  fromIpld
  | Ipld.array #[Ipld.number ENV, l, n, u, uM, e, eM, c, cM, es] => do
    Env.mk <$> fromIpld l <*> fromIpld n
      <*> fromIpld u <*> fromIpld uM
      <*> fromIpld e <*> fromIpld eM
      <*> fromIpld c <*> fromIpld cM 
      <*> fromIpld es
  | other => throw (IpldError.Expected "Object")

end Radiya



