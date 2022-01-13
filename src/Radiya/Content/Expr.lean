import Radiya.Ipld.Ipld
import Radiya.Ipld.Cid
import Radiya.Content.Cid
import Radiya.Ipld.Multihash
import Radiya.Ipld.DagCbor
import Radiya.ToIpld

import Lean.Expr

open Lean (BinderInfo Literal)

namespace Radiya.Content

inductive Expr where
| var   : Nat → Expr
| sort  : UnivCid → Expr
| const : ConstCid → List UnivCid → Expr
| app   : ExprCid → ExprCid → Expr
| lam   : ExprCid → ExprCid → Expr
| pi    : ExprCid → ExprCid → Expr
| letE  : ExprCid → ExprCid → ExprCid → Expr
| lit   : LitCid → Expr
| fix   : ExprCid → Expr

open ToIpld
open Ipld

instance : ToIpld (Lean.BinderInfo) where
  toIpld
  | BinderInfo.default => Ipld.number 0
  | BinderInfo.implicit => Ipld.number 1
  | BinderInfo.strictImplicit => Ipld.number 2
  | BinderInfo.instImplicit => Ipld.number 3
  | BinderInfo.auxDecl => Ipld.number 4

  fromIpld
  | Ipld.number 0 => return BinderInfo.default
  | Ipld.number 1 => return BinderInfo.implicit
  | Ipld.number 2 => return BinderInfo.strictImplicit
  | Ipld.number 3 => return BinderInfo.instImplicit
  | Ipld.number 4 => return BinderInfo.auxDecl
  | _ => throw $ IpldError.Expected "BinderInfo"

instance : ToIpld (Lean.Literal) where
  toIpld
  | Literal.natVal n => array #[number LITERAL, number 0, toIpld n]
  | Literal.strVal s => array #[number LITERAL, number 1, toIpld s]

  fromIpld
  | array #[number LITERAL, number 0, n] => Literal.natVal <$> fromIpld n
  | array #[number LITERAL, number 1, s] => Literal.strVal <$> fromIpld s
  | _ => throw $ IpldError.Expected "Literal"

instance : ToIpld Expr where
  toIpld
  | Expr.var n      => array #[number EXPR, number 0, toIpld n]
  | Expr.sort u     => array #[number EXPR, number 1, toIpld u]
  | Expr.const c ls => array #[number EXPR, number 2, toIpld c, toIpld ls]
  | Expr.app f a    => array #[number EXPR, number 3, toIpld f, toIpld a]
  | Expr.lam t b    => array #[number EXPR, number 4, toIpld t, toIpld b]
  | Expr.pi t b     => array #[number EXPR, number 5, toIpld t, toIpld b]
  | Expr.letE t v b => array #[number EXPR, number 6, toIpld t, toIpld v, toIpld b]
  | Expr.lit l      => array #[number EXPR, number 7, toIpld l]
  | Expr.fix b      => array #[number EXPR, number 8, toIpld b]

  fromIpld
  | array #[number EXPR, number 0, n]       => Expr.var <$> fromIpld n
  | array #[number EXPR, number 1, u]       => Expr.sort <$> fromIpld u
  | array #[number EXPR, number 2, c, ls]   => Expr.const <$> fromIpld c <*> fromIpld ls
  | array #[number EXPR, number 3, f, a]    => Expr.app <$> fromIpld f <*> fromIpld a
  | array #[number EXPR, number 4, t, b]    => Expr.lam <$> fromIpld t <*> fromIpld b
  | array #[number EXPR, number 5, t, b]    => Expr.pi <$> fromIpld t <*> fromIpld b
  | array #[number EXPR, number 6, t, v, b] => Expr.letE <$> fromIpld t <*> fromIpld v <*> fromIpld b
  | array #[number EXPR, number 7, l]       => Expr.lit <$> fromIpld l
  | array #[number EXPR, number 8, b]       => Expr.fix <$> fromIpld b
  | _ => throw (IpldError.Expected "Expr")

inductive ExprMeta where
| var   : ExprMeta
| sort  : UnivMetaCid → ExprMeta
| const : NameCid → ConstMetaCid → List UnivMetaCid → ExprMeta
| app   : ExprMetaCid → ExprMetaCid → ExprMeta
| lam   : BinderInfo → NameCid → ExprMetaCid → ExprMetaCid → ExprMeta
| pi    : BinderInfo → NameCid → ExprMetaCid → ExprMetaCid → ExprMeta
| letE  : NameCid → ExprMetaCid → ExprMetaCid → ExprMetaCid → ExprMeta
| lit   : ExprMeta
| fix   : NameCid → ExprMetaCid → ExprMeta

instance : ToIpld ExprMeta where
  toIpld
  | ExprMeta.var          => array #[number EXPRMETA, number 0]
  | ExprMeta.sort u       => array #[number EXPRMETA, number 1, toIpld u]
  | ExprMeta.const n c ls => array #[number EXPRMETA, number 2, toIpld n, toIpld c, toIpld ls]
  | ExprMeta.app f a      => array #[number EXPRMETA, number 3, toIpld f, toIpld a]
  | ExprMeta.lam i n t b  => array #[number EXPRMETA, number 4, toIpld i, toIpld n, toIpld t, toIpld b]
  | ExprMeta.pi i n t b   => array #[number EXPRMETA, number 5, toIpld i, toIpld n, toIpld t, toIpld b]
  | ExprMeta.letE n t v b => array #[number EXPRMETA, number 6, toIpld n, toIpld t, toIpld v, toIpld b]
  | ExprMeta.lit          => array #[number EXPRMETA, number 7]
  | ExprMeta.fix n b      => array #[number EXPRMETA, number 8, toIpld n, toIpld b]

  fromIpld
  | array #[number EXPRMETA, number 0]             => return ExprMeta.var
  | array #[number EXPRMETA, number 1, u]          => ExprMeta.sort <$> fromIpld u
  | array #[number EXPRMETA, number 2, n, c, ls]   => ExprMeta.const <$> fromIpld n <*> fromIpld c <*> fromIpld ls
  | array #[number EXPRMETA, number 3, f, a]       => ExprMeta.app <$> fromIpld f <*> fromIpld a
  | array #[number EXPRMETA, number 4, i, n, t, b] => ExprMeta.lam <$> fromIpld i <*> fromIpld n <*> fromIpld t <*> fromIpld b
  | array #[number EXPRMETA, number 5, i, n, t, b] => ExprMeta.pi <$> fromIpld i <*> fromIpld n <*> fromIpld t <*> fromIpld b
  | array #[number EXPRMETA, number 6, n, t, v, b] => ExprMeta.letE <$> fromIpld n <*> fromIpld t <*> fromIpld v <*> fromIpld b
  | array #[number EXPRMETA, number 7]             => return ExprMeta.lit
  | array #[number EXPRMETA, number 8, n, b]       => ExprMeta.fix <$> fromIpld n <*> fromIpld b
  | _ => throw (IpldError.Expected "ExprMeta")

end Radiya.Content
