module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RG24Data
public import CFSG.Certificates.Kernel.Misc.G24P0Sound
public import Certificates.Kernel.Ronan148.G24P0Checks
public import Certificates.Kernel.Misc.G24Facts

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Ronan148.G24P0

open CFSG.KC.Misc.G24 CFSG.KD.Misc.G24 CFSG.LieType.Multipliers.G24
open CFSG.RankThree.PartTwo.Sec4.Ronan148R.G24P

theorem bWord (w : List (Fin 6 × Bool)) : toMat 14 (wordArr w) = g24Mat GR w := by
  rw [g24Mat, ← bG]
  rfl

theorem b1 : p1Word = parseWord (strOf p1C) := rfl

theorem b2 : p2Word = parseWord (strOf p2C) := rfl

theorem bZ : z0Word = parseWord (strOf (nthL XS 5)) ++ parseWord (strOf (nthL YS 5)) := by
  rw [CFSG.KC.Misc.Spec.nthL_eq, CFSG.KC.Misc.Spec.nthL_eq, z0Word, genWordX, genWordY, bX, bY]
  exact congrArg₂ (· ++ ·) (congrArg parseWord (List.getD_map XS [] (n := 5) strOf))
    (congrArg parseWord (List.getD_map YS [] (n := 5) strOf))

theorem facts : toMat 14 (p1Arr ()) ^ 3 = 1 ∧ toMat 14 (p2Arr ()) ^ 3 = 1 ∧
    toMat 14 (p1Arr ()) * toMat 14 (p2Arr ()) * toMat 14 (p1Arr ()) ^ 2 *
      toMat 14 (p2Arr ()) ^ 2 = toMat 14 (z0Arr ()) ∧
    toMat 14 (z0Arr ()) * toMat 14 (p1Arr ()) = toMat 14 (p1Arr ()) * toMat 14 (z0Arr ()) ∧
    toMat 14 (z0Arr ()) * toMat 14 (p2Arr ()) = toMat 14 (p2Arr ()) * toMat 14 (z0Arr ()) ∧
    toMat 14 (z0Arr ()) ≠ 1 := by
  rw [p1Arr, p2Arr, z0Arr, bWord, bWord, bWord, b1, b2, bZ]
  exact g24P0_sound k44 kP0

end CFSG.KD.Ronan148.G24P0

end
