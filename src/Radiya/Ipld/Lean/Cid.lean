import Ipld.Cid
import Ipld.Ipld
import Ipld.Lean.ToIpld

def LITERAL: UInt64 := 0xC0DE0000
def NAME: UInt64 := 0x3E7A0000
def UNIV: UInt64 := 0xC0DE0001
def UNIVMETA: UInt64 := 0x3E7A0001
def EXPR: UInt64 := 0xC0DE0002
def EXPRMETA: UInt64 := 0x3E7A0002
def CONST: UInt64 := 0xC0DE0003
def CONSTMETA: UInt64 := 0x3E7A0003

def ENV: UInt64 := 0xC0DE0004

structure LitCid where data : Cid
structure NameCid where data : Cid
structure UnivCid where data : Cid
structure UnivMetaCid where data : Cid
structure ExprCid where data : Cid
structure ExprMetaCid where data : Cid
structure ConstCid where data : Cid
structure ConstMetaCid where data : Cid
structure EnvCid where data : Cid

instance : ToIpld LitCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == LITERAL.toNat then Except.ok (LitCid.mk n)
    else Except.error (IpldError.Expected "Literal Cid")
  | _ => Except.error (IpldError.Expected "Literal Cid")

instance : ToString LitCid where
  toString x := toString x.data

instance : ToIpld NameCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == NAME.toNat then Except.ok (NameCid.mk n)
    else Except.error (IpldError.Expected "Name Cid")
  | _ => Except.error (IpldError.Expected "Name Cid")

instance : ToString NameCid where
  toString x := toString x.data

instance : ToIpld UnivCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == UNIV.toNat then Except.ok (UnivCid.mk n)
    else Except.error (IpldError.Expected "Universe Cid")
  | _ => Except.error (IpldError.Expected "Universe Cid")

instance : ToString UnivCid where
  toString x := toString x.data

instance : ToIpld UnivMetaCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == UNIVMETA.toNat then Except.ok (UnivMetaCid.mk n)
    else Except.error (IpldError.Expected "Universe Meta Cid")
  | _ => Except.error (IpldError.Expected "Universe Meta Cid")

instance : ToString UnivMetaCid where
  toString x := toString x.data

instance : ToIpld ExprCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == EXPR.toNat then Except.ok (ExprCid.mk n)
    else Except.error (IpldError.Expected "Expression Cid")
  | _ => Except.error (IpldError.Expected "Expression Cid")

instance : ToString ExprCid where
  toString x := toString x.data

instance : ToIpld ExprMetaCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == EXPRMETA.toNat then Except.ok (ExprMetaCid.mk n)
    else Except.error (IpldError.Expected "Expression Meta Cid")
  | _ => Except.error (IpldError.Expected "Expression Meta Cid")

instance : ToString ExprMetaCid where
  toString x := toString x.data

instance : ToIpld ConstCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == CONST.toNat then Except.ok (ConstCid.mk n)
    else Except.error (IpldError.Expected "Constant Cid")
  | _ => Except.error (IpldError.Expected "Constant Cid")

instance : ToString ConstCid where
  toString x := toString x.data

instance : ToIpld ConstMetaCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == CONSTMETA.toNat then Except.ok (ConstMetaCid.mk n)
    else Except.error (IpldError.Expected "Constant Meta Cid")
  | _ => Except.error (IpldError.Expected "Constant Meta Cid")

instance : ToString ConstMetaCid where
  toString x := toString x.data

instance : ToIpld EnvCid where
  toIpld n := Ipld.link n.data
  fromIpld
  | Ipld.link n => if n.codec == ENV.toNat then Except.ok (EnvCid.mk n)
    else Except.error (IpldError.Expected "Constant Meta Cid")
  | _ => Except.error (IpldError.Expected "Constant Meta Cid")

instance : ToString EnvCid where
  toString x := toString x.data
