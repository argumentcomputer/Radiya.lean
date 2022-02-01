import Radiya.Optics.Lens

universe u

namespace Optics

inductive Either (L R : Type u)
  | left : L → Either L R
  | right : R → Either L R

structure Prism (a b s t : Type u) : Type u where
  match : s → Either t a
  build : b → t

structure Adapter (a b s t : Type u) : Type u where
  from : s → a
  to : b → t

structure Traversal (a b s t : Type u) : Type u where
  extract : s → {sub : (la : List a) × (lb : List b → t) // sub.la.size = sub.lb.size }  

variable (P : Type u → Type u → Type u)

class Profunctor (P : Type u → Type u → Type u) where
  dimap : {A A' B B' : Type u} → (f : A' → A) → (g : B → B') → P A B → P A' B'

class Cartesian (P : Type u → Type u → Type u) [Profunctor P] where
  first : {A B C : Type u} → (p : P A B) → P (A × C) (B × C)
  second : {A B C : Type u} → (p : P A B) → P (C × A) (C × B)

class CoCartesian (P : Type u → Type u → Type u) [Profunctor P] where
  left : {A B C : Type u} → (p : P A B) → P (Either A C) (Either B C)
  right : {A B C : Type u} → (p : P A B) → P (Either C A) (Either C B)

class Monodial (P : Type u → Type u → Type u) [Profunctor P] where
  empty : (p : P PUnit PUnit)
  madd : {A B C D : Type u} → (p1 : P A B) → (p2 : P C D) → P (A × C) (B × C)

instance {A B : Type u} : Profunctor (Lens A B) where
  dimap f g := Lens.mk {get := get ∘ f, set := g ∘ set ∘ mapFst f : Para}

end Optics
