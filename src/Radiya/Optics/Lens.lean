import Radiya.Optics.FreePara

namespace Optics
universe u v

/-
A lens from focus a to focus b with structure s and t before and after action.
-/
def Lens (a b s t : Type u) : Type u := Para [] [] a b s t

def Lens' (s a : Type u) : Type u := Lens s s a a 

end Optics
