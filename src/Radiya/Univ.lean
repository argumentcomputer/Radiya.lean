namespace Radiya

inductive Univ where
| zero
| succ : Univ → Univ
| max : Univ → Univ → Univ
| imax : Univ → Univ → Univ
| param : Nat → Univ
deriving Inhabited, BEq

def instantiateUniv (u : Univ) (idx : Nat)(subst : Univ) : Univ :=
  match u with
  | Univ.succ u => Univ.succ (instantiateUniv u idx subst)
  | Univ.max a b => Univ.max (instantiateUniv a idx subst) (instantiateUniv b idx subst)
  | Univ.imax a b => Univ.imax (instantiateUniv a idx subst) (instantiateUniv b idx subst)
  | Univ.param idx' => if idx == idx' then subst else u
  | Univ.zero => u

def combining (a b : Univ) : Univ :=
  match a, b with
  | Univ.zero, _ => b
  | _, Univ.zero => a
  | Univ.succ a, Univ.succ b => Univ.succ (combining a b)
  | _, _ => Univ.max a b

def simplify (u : Univ) : Univ :=
  match u with
  | Univ.succ u' => Univ.succ (simplify u')
  | Univ.max a b => Univ.max (simplify a) (simplify b)
  | Univ.imax a b =>
    let b_prime := simplify b
    match b_prime with
    | Univ.zero => Univ.zero
    | Univ.succ _ => combining (simplify a) b_prime
    | _ => Univ.imax (simplify a) b_prime
  | _ => u

partial def leqCore (a b : Univ) (diff : Int) : Bool :=
  if a == b && diff >= 0 then true
  else match a, b with
  | Univ.zero, Univ.zero => diff >= 0
  | Univ.param x, Univ.param y => x == y && diff >= 0
  | Univ.zero, Univ.param _ => diff >= 0
  | Univ.param _, Univ.zero => false
  | Univ.succ a, _ => leqCore a b (diff - 1)
  | _, Univ.succ b => leqCore a b (diff + 1)
  | Univ.max a₁ a₂, b => leqCore a₁ b diff && leqCore a₂ b diff
  | a, Univ.max b₁ b₂ => leqCore a b₁ diff || leqCore a b₂ diff
  | Univ.imax _ (Univ.param idx), _ =>
    let succ := Univ.succ (Univ.param idx)
    leqCore (instantiateUniv a idx Univ.zero) (instantiateUniv b idx Univ.zero) diff &&
    leqCore (instantiateUniv a idx succ) (instantiateUniv b idx succ) diff
  | _, Univ.imax _ (Univ.param idx) =>
    let succ := Univ.succ (Univ.param idx)
    leqCore (instantiateUniv a idx Univ.zero) (instantiateUniv b idx Univ.zero) diff &&
    leqCore (instantiateUniv a idx succ) (instantiateUniv b idx succ) diff
  | Univ.imax a₁ (Univ.max a₂ a₃), _ =>
    let new_max := Univ.max (Univ.imax a₁ a₂) (Univ.imax a₁ a₃)
    leqCore new_max b diff
  | Univ.imax a₁ (Univ.imax a₂ a₃), _ =>
    let new_max := Univ.max (Univ.imax a₁ a₃) (Univ.imax a₂ a₃)
    leqCore new_max b diff
  | _, Univ.imax b₁ (Univ.max b₂ b₃) =>
    let new_max := Univ.max (Univ.imax b₁ b₂) (Univ.imax b₁ b₃)
    leqCore a new_max diff
  | _, Univ.imax b₁ (Univ.imax b₂ b₃) =>
    let new_max := Univ.max (Univ.imax b₁ b₃) (Univ.imax b₂ b₃)
    leqCore a new_max diff
  | _, _ => panic! "Impossible case"

partial def equalUniv (u u' : Univ) : Bool :=
  let u := simplify u
  let u' := simplify u'
  leqCore u u' 0 && leqCore u' u 0

def equalUnivs (us us' : List Univ) : Bool :=
  match us, us' with
  | [], [] => true
  | u::us, u'::us' => equalUniv u u' && equalUnivs us us'
  | _, _ => false

end Radiya
