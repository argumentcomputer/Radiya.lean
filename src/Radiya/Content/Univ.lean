import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Content.Cid
import Radiya.Content.ToIpld
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor

namespace Radiya.Content

inductive Univ where
| zero
| succ : UnivCid → Univ
| max : UnivCid → UnivCid → Univ
| imax : UnivCid → UnivCid → Univ
| param : Nat → Univ

open ToIpld
open Ipld

instance : ToIpld Univ where
  toIpld
  | Univ.zero     => array #[number UNIV, number 0]
  | Univ.succ p   => array #[number UNIV, number 1, toIpld p]
  | Univ.max x y  => array #[number UNIV, number 2, toIpld x, toIpld y]
  | Univ.imax x y => array #[number UNIV, number 3, toIpld x, toIpld y]
  | Univ.param i  => array #[number UNIV, number 4, toIpld i]

  fromIpld
  | array #[number UNIV, number 0]       => Univ.zero
  | array #[number UNIV, number 1, p]    => Univ.succ <$> fromIpld p
  | array #[number UNIV, number 2, x, y] => Univ.max <$> fromIpld x <*> fromIpld y
  | array #[number UNIV, number 3, x, y] => Univ.imax <$> fromIpld x <*> fromIpld y
  | array #[number UNIV, number 4, i]    => Univ.param <$> fromIpld i
  | _ => throw (IpldError.Expected "Univ")

inductive UnivMeta where
| zero
| succ : UnivMetaCid → UnivMeta
| max : UnivMetaCid → UnivMetaCid → UnivMeta
| imax : UnivMetaCid → UnivMetaCid → UnivMeta
| param : NameCid → UnivMeta

instance : ToIpld UnivMeta where
  toIpld
  | UnivMeta.zero     => Ipld.array #[Ipld.number UNIVMETA, Ipld.number 0]
  | UnivMeta.succ p   => Ipld.array #[Ipld.number UNIVMETA, Ipld.number 1, toIpld p]
  | UnivMeta.max x y  => Ipld.array #[Ipld.number UNIVMETA, Ipld.number 2, toIpld x, toIpld y]
  | UnivMeta.imax x y => Ipld.array #[Ipld.number UNIVMETA, Ipld.number 3, toIpld x, toIpld y]
  | UnivMeta.param n  => Ipld.array #[Ipld.number UNIVMETA, Ipld.number 4, toIpld n]

  fromIpld
  | array #[number UNIVMETA, number 0]       => UnivMeta.zero
  | array #[number UNIVMETA, number 1, p]    => UnivMeta.succ <$> fromIpld p
  | array #[number UNIVMETA, number 2, x, y] => UnivMeta.max <$> fromIpld x <*> fromIpld y
  | array #[number UNIVMETA, number 3, x, y] => UnivMeta.imax <$> fromIpld x <*> fromIpld y
  | array #[number UNIVMETA, number 4, n]    => UnivMeta.param <$> fromIpld n
  | _ => throw (IpldError.Expected "UnivMeta")

end Radiya.Content
