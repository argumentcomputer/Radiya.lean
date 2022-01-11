import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor


inductive IpldError where
| Expected (x: String)

class ToIpld (α : Type) where
  toIpld : α -> Ipld
  fromIpld : Ipld -> Except IpldError α

instance : ToIpld String where
  toIpld s := Ipld.string s
  fromIpld
  | Ipld.string s => Except.ok s
  | _ => Except.error (IpldError.Expected "String")

instance : ToIpld UInt64 where
  toIpld s := Ipld.number s
  fromIpld
  | Ipld.number x => Except.ok x
  | _ => Except.error (IpldError.Expected "UInt64")

instance : ToIpld Nat where
  toIpld x := Ipld.bytes x.toByteArrayBE
  fromIpld
  | Ipld.bytes x => Except.ok x.fromByteArrayBE
  | _ => Except.error (IpldError.Expected "Nat")

def List.toIpldAux {α : Type} [inst : ToIpld α] (xs: List α): Ipld :=
  Ipld.array (Array.mk (xs.map (@ToIpld.toIpld α inst)))

def List.fromIpldAux {α: Type} [inst: ToIpld α] (xs: Array Ipld): Except IpldError (List α) :=
  List.mapM (@ToIpld.fromIpld α inst) xs.data

instance List.ToIpld {α : Type} [inst : ToIpld α] : ToIpld (List α) where
  toIpld := List.toIpldAux
  fromIpld
  | Ipld.array x => List.fromIpldAux x
  | _ => Except.error (IpldError.Expected "Array")
