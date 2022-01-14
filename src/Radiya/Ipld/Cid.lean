import Radiya.Ipld.Multihash
import Radiya.Ipld.Multibase
import Radiya.Ipld.Utils
import Radiya.Ipld.UnsignedVarint

import Init.Data.Ord

structure Cid where
  version : Nat
  codec: Nat
  hash: Multihash
  deriving BEq, Inhabited, Repr

namespace Cid

def toBytes (self : Cid) : ByteArray :=
 (UnsignedVarint.toVarInt self.version) ++ (UnsignedVarint.toVarInt self.codec) ++ Multihash.toBytes self.hash

def toString (self: Cid) : String :=
  Multibase.encode Multibase.Base32 (toBytes self).toList

instance : ToString Cid where
  toString := toString

def fromBytes (bytes : ByteArray) : Option Cid :=
  Option.bind (UnsignedVarint.fromVarInt bytes) $ fun (version, bytes) =>
  Option.bind (UnsignedVarint.fromVarInt bytes) $ fun (codec, bytes) =>
  Option.bind (Multihash.fromBytes bytes) $ fun hash =>
  some { version, codec, hash }

def fromString (str: String) : Option Cid := 
  Option.bind (Multibase.decode Multibase.Base32 str) $ fun bytes =>
  fromBytes (ByteArray.mk $ Array.mk bytes)

instance : Ord Cid where
  compare x y := compare x.toBytes y.toBytes

namespace Test

def ex1 : Cid := { version := 0x1, codec := 0x11, hash := Multihash.Test.ex1 }

#eval ex1
#eval toBytes ex1
#eval fromBytes (toBytes ex1)

end Test

end Cid
