namespace Radiya

inductive Univ where
| zero
| succ : Univ → Univ
| max : Univ → Univ → Univ
| imax : Univ → Univ → Univ
| param : Nat → Univ

end Radiya
