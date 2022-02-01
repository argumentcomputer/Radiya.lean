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


structure Para (p q : List (Type u)) (a b s t : Type u) : Type u where
  get : toProd s p → a
  set : toProd s p × b → toProd t q

