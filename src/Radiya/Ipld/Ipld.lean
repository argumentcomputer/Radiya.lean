import Radiya.Ipld.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.Utils
import Std.Data.RBTree

open Std (RBNode)

def toList (map : RBNode α (fun _ => β)) : List (α × β) :=
  map.revFold (fun as a b => (a,b)::as) []

instance [BEq α] [BEq β] : BEq (RBNode α fun _ => β) where
  beq a b := toList a == toList b

instance : BEq Cid where
  beq a b := a.version == b.version && a.codec == b.codec && a.hash == b.hash

inductive Ipld where
| null
| bool (b : Bool)
| number (n : UInt64)
| string (s : String)
| bytes (b : ByteArray)
| array (elems : Array Ipld)
| object (kvPairs : RBNode String (fun _ => Ipld))
| link (cid: Cid)
deriving BEq, Inhabited

namespace Ipld

def nodeToList (map : RBNode String (fun _ => Ipld)) : List (String × Ipld) :=
  map.revFold (fun as a b => (a,b)::as) []

mutual
partial def listToStringAux : List Ipld → String
  | []    => ""
  | x::xs => ", " ++ toStringAux x ++ listToStringAux xs

partial def objectToStringAux : List (String × Ipld) → String
  | []    => ""
  | (n,x)::xs => "; " ++ n ++ " " ++ toStringAux x ++ objectToStringAux xs

partial def toStringAux : Ipld -> String
| Ipld.null =>  "null"
| Ipld.bool b  =>  toString b 
| Ipld.number n  =>  toString n
| Ipld.string n  =>  toString n
| Ipld.bytes n  =>  toString n
| Ipld.array n  =>  "[" ++ listToStringAux n.data ++ "]"
| Ipld.object n  =>  "{" ++ objectToStringAux (nodeToList n) ++ "}"
| Ipld.link n => toString n
end

end Ipld

instance : ToString Ipld where
   toString := Ipld.toStringAux

instance Ipld.Repr : Repr Ipld where
  reprPrec
  | Ipld.null, prec => Repr.addAppParen ("Ipld.null") prec
  | Ipld.bool b, prec => Repr.addAppParen ("Ipld.bool " ++ toString b) prec
  | Ipld.number n, prec => Repr.addAppParen ("Ipld.number " ++ toString n) prec
  | Ipld.string n, prec => Repr.addAppParen ("Ipld.string " ++ toString n) prec
  | Ipld.bytes n, prec => Repr.addAppParen ("Ipld.bytes " ++ toString n) prec
  | Ipld.link n, prec => Repr.addAppParen ("Ipld.link " ++ toString n) prec
  | Ipld.array n, prec => Repr.addAppParen ("Ipld.array " ++ toString n) prec
  | Ipld.object n, prec => Repr.addAppParen ("Ipld.object " ++ toString (Ipld.object n)) prec

namespace Ipld

def mkObject (o : List (String × Ipld)) : Ipld :=
  object <| Id.run <| do
    let mut kvPairs := RBNode.leaf
    for (k, v) in o do
      kvPairs := kvPairs.insert compare k v
    kvPairs

end Ipld
