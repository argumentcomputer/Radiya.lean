namespace Optics
universe u v

@[specialize]
def toProd (h : Type u) (p : List (Type u)) : Type u :=
  match p with 
  | [] => h
  | n :: tail => h × toProd n tail

@[specialize]
def toForAll (h : Type u) (p : List (Type u)) : Type u :=
  match p with 
  | [] => h
  | n :: tail => h → toForAll n tail


structure Params (p q : List (Type u)) (a b s t : Type u) : Type u where
  get : toProd s p → a
  set : toProd s p × b → toProd t q

/-
A lens from focus a to focus b with structure s and t before and after action.
-/
def Lens (a b s t : Type u) : Type u := Params [] [] a b s t

def Lens' (s a : Type u) : Type u := Lens s s a a 

end Optics
