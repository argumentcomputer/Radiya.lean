import Ipld.Ipld
import Ipld.Cid
import Ipld.Multihash
import Ipld.DagCbor


inductive IpldError where
| Expected (x: String)

class ToIpld (α : Type) where
  toIpld : α -> Ipld
  fromIpld : Ipld -> Except IpldError α




