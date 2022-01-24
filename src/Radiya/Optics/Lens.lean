namespace Optics
universe u v

def fromList (p : List (Type u)) : Type v := p.foldl (λ a b => a × b)

structure Params (p q : List (Type u)) (a b s t : Type u) where
  get : fromList (List.cons s p) → a
  set : fromList (List.cons s p) × b → fromList (List.cons t q)

/-
A lens from a to b
-/
def Lens (a b s t : Type u) : Type v := Params [] []

end Optics
