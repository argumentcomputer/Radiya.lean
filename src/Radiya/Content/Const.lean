import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor
import Radiya.Content.ToIpld
import Radiya.Content.Cid

import Lean.Declaration

open Lean (QuotKind DefinitionSafety)

namespace Radiya.Content

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
| defn     : Nat → ExprCid → ExprCid → DefinitionSafety → Const
| induct   : Nat → ExprCid → Nat → Nat → List Intro → Bool → Const
| ctor     : Nat → ExprCid → ConstCid → Nat → Nat → Nat → Bool → Const
| recursor : Nat → ExprCid → ConstCid → Nat → Nat → Nat → Nat → List RecRule → Bool → Bool → Const

open ToIpld
open Ipld

instance : ToIpld RecRule where
  toIpld x := array #[toIpld x.ctor, toIpld x.fields, toIpld x.rhs]
  fromIpld
  | array #[ctor, fields, rhs] => RecRule.mk <$> fromIpld ctor <*> fromIpld fields <*> fromIpld rhs
  | _ => throw (IpldError.Expected "RecRule")

instance : ToIpld Intro where
  toIpld x := array #[toIpld x.ctor, toIpld x.typ]
  fromIpld
  | array #[ctor, typ] => Intro.mk <$> fromIpld ctor <*> fromIpld typ
  | _ => throw (IpldError.Expected "Intro")

instance : ToIpld QuotKind where
  toIpld
  | QuotKind.type => number 0
  | QuotKind.ctor => number 1
  | QuotKind.lift => number 2
  | QuotKind.ind  => number 3

  fromIpld
  | number 0 => return QuotKind.type
  | number 1 => return QuotKind.ctor
  | number 2 => return QuotKind.lift
  | number 3 => return QuotKind.ind
  | _ => throw (IpldError.Expected "QuotKind")

instance : ToIpld DefinitionSafety where
  toIpld
  | DefinitionSafety.«unsafe» => number 0
  | DefinitionSafety.safe => number 1
  | DefinitionSafety.«partial» => number 2

  fromIpld
  | number 0 => return DefinitionSafety.«unsafe»
  | number 1 => return DefinitionSafety.safe
  | number 2 => return DefinitionSafety.«partial»
  | _ => throw (IpldError.Expected "DefinitionSafety")

instance : ToIpld Const where
  toIpld
  | Const.quotient l t k      => array #[number CONST, number 0, toIpld l, toIpld t, toIpld k]
  | Const.axiomC l t s u      => array #[number CONST, number 1, toIpld l, toIpld t, toIpld s, toIpld u]
  | Const.theoremC l t v      => array #[number CONST, number 2, toIpld l, toIpld t, toIpld v]
  | Const.opaque l t v s u    => array #[number CONST, number 3, toIpld l, toIpld t, toIpld v, toIpld s, toIpld u]
  | Const.defn l t v s        => array #[number CONST, number 4, toIpld l, toIpld t, toIpld v, toIpld s]
  | Const.induct l t p i is s => array #[number CONST, number 5, toIpld l, toIpld t, toIpld p, toIpld i, toIpld is, toIpld s]
  | Const.ctor l t i c p f s  => array #[number CONST, number 6, toIpld l, toIpld t, toIpld i, toIpld c, toIpld p, toIpld f, toIpld s]
  | Const.recursor l t i p i' m m' rs k s =>
      array #[number CONST, number 7, toIpld l, toIpld t, toIpld i, toIpld p, toIpld i', toIpld m, toIpld m', toIpld rs, toIpld k, toIpld s]

  fromIpld
  | array #[number CONST, number 0, l, t, k] =>
    Const.quotient <$> fromIpld l <*> fromIpld t <*> fromIpld k
  | array #[number CONST, number 1, l, t, s, u] =>
    Const.axiomC <$> fromIpld l <*> fromIpld t <*> fromIpld s <*> fromIpld u
  | array #[number CONST, number 2, l, t, v] =>
    Const.theoremC <$> fromIpld l <*> fromIpld t <*> fromIpld v
  | array #[number CONST, number 3, l, t, v, s, u] =>
    Const.opaque <$> fromIpld l <*> fromIpld t <*> fromIpld v <*> fromIpld s <*> fromIpld u
  | array #[number CONST, number 4, l, t, v, s] =>
    Const.defn <$> fromIpld l <*> fromIpld t <*> fromIpld v <*> fromIpld s
  | array #[number CONST, number 5, l, t, p, i, is, s] =>
    Const.induct <$> fromIpld l <*> fromIpld t <*> fromIpld p <*> fromIpld i <*> fromIpld is <*> fromIpld s
  | array #[number CONST, number 6, l, t, i, c, p, f, s] => 
    Const.ctor <$> fromIpld l <*> fromIpld t <*> fromIpld i <*> fromIpld c <*> fromIpld p <*> fromIpld f <*> fromIpld s
  | array #[number CONST, number 7, l, t, i, p, i', m, m', rs, k, s] => do
    let levels : Nat <- fromIpld l
    let typ : ExprCid <- fromIpld t
    let induct : ConstCid <- fromIpld i
    let params : Nat <- fromIpld p
    let indices : Nat <- fromIpld i'
    let motives : Nat <- fromIpld m
    let minors  : Nat <- fromIpld m'
    let rules : List RecRule <- fromIpld rs
    let k : Bool <- fromIpld k
    let s : Bool <- fromIpld s
    return Const.recursor levels typ induct params indices motives minors rules k s
  | _ => throw (IpldError.Expected "Const")

inductive ConstMeta where
| quotient : NameCid → List NameCid → ExprCid → ConstMeta
| axiomC   : NameCid → List NameCid → ExprCid → ConstMeta
| theoremC : NameCid → List NameCid → ExprCid → ExprCid → ConstMeta
| opaque   : NameCid → List NameCid → ExprCid → ExprCid → ConstMeta
| defn     : NameCid → List NameCid → ExprCid → ExprCid → ConstMeta
| induct   : NameCid → List NameCid → ExprCid → List ExprMetaCid → ConstMeta
| ctor     : NameCid → List NameCid → ExprCid → ConstMetaCid → ConstMeta
| recursor : NameCid → List NameCid → ExprCid → List ExprMetaCid → ConstMeta

instance : ToIpld ConstMeta where
  toIpld
  | ConstMeta.quotient n l t    => array #[number CONSTMETA, number 0, toIpld n, toIpld l, toIpld t]
  | ConstMeta.axiomC n l t      => array #[number CONSTMETA, number 1, toIpld n, toIpld l, toIpld t]
  | ConstMeta.theoremC n l t v  => array #[number CONSTMETA, number 2, toIpld n, toIpld l, toIpld t, toIpld v]
  | ConstMeta.opaque n l t v    => array #[number CONSTMETA, number 3, toIpld n, toIpld l, toIpld t, toIpld v]
  | ConstMeta.defn n l t v      => array #[number CONSTMETA, number 4, toIpld n, toIpld l, toIpld t, toIpld v]
  | ConstMeta.induct n l t is   => array #[number CONSTMETA, number 5, toIpld n, toIpld l, toIpld t, toIpld is]
  | ConstMeta.ctor n l t i      => array #[number CONSTMETA, number 6, toIpld n, toIpld l, toIpld t, toIpld i]
  | ConstMeta.recursor n l t rs => array #[number CONSTMETA, number 7, toIpld n, toIpld l, toIpld t, toIpld rs]

  fromIpld
  | array #[number CONSTMETA, number 0, n, l, t] =>
    ConstMeta.quotient <$> fromIpld n <*> fromIpld l <*> fromIpld t
  | array #[number CONSTMETA, number 1, n, l, t] =>
    ConstMeta.axiomC <$> fromIpld n <*> fromIpld l <*> fromIpld t
  | array #[number CONSTMETA, number 2, n, l, t, v] =>
    ConstMeta.theoremC <$> fromIpld n <*> fromIpld l <*> fromIpld t <*> fromIpld v
  | array #[number CONSTMETA, number 3, n, l, t, v] =>
    ConstMeta.opaque <$> fromIpld n <*> fromIpld l <*> fromIpld t <*> fromIpld v
  | array #[number CONSTMETA, number 4, n, l, t, v] =>
    ConstMeta.defn <$> fromIpld n <*> fromIpld l <*> fromIpld t <*> fromIpld v
  | array #[number CONSTMETA, number 5, n, l, t, is] =>
    ConstMeta.induct <$> fromIpld n <*> fromIpld l <*> fromIpld t <*> fromIpld is
  | array #[number CONSTMETA, number 6, n, l, t, i] =>
    ConstMeta.ctor <$> fromIpld n <*> fromIpld l <*> fromIpld t <*> fromIpld i
  | array #[number CONSTMETA, number 7, n, l, t, rs] =>
    ConstMeta.ctor <$> fromIpld n <*> fromIpld l <*> fromIpld t <*> fromIpld rs
  | _ => throw (IpldError.Expected "ConstMeta")

end Radiya.Content
