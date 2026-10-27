module

public import Certificates.Data.Eight89KModels
public import Certificates.Data.Kernel.PackPerm

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.PackPerm

public section

namespace CFSG.KC.Eight89K

@[expose] def abb5 : List Nat := (List.replicate 5 [0, 1, 1]).flatten

@[expose] def eqs3 : List (List Nat × List Nat) :=
  [(KData.sW 15, []), (0 :: KData.sW 5, KData.sW 5 ++ [0]), (1 :: KData.sW 5, KData.sW 5 ++ [1]),
    ([0, 0], []), ([1, 1, 1, 1], []), (abb5, [])]

@[expose] def neqs3 : List (List Nat) := [KData.sW 3, KData.sW 5]

@[expose] def eqs6 : List (List Nat × List Nat) :=
  [(KData.sW 30, []), (0 :: KData.sW 5, KData.sW 5 ++ [0]), (1 :: KData.sW 5, KData.sW 5 ++ [1]),
    ([0, 0], KData.sW 15), ([1, 1, 1, 1], KData.sW 15), (abb5, [])]

@[expose] def neqs6 : List (List Nat) := [KData.sW 15, KData.sW 10, KData.sW 6]

theorem model3_rel :
    relCheck 18 KData.m3aT.toList KData.m3bT.toList eqs3 neqs3 = true := by
  decide +kernel

theorem model6_rel :
    relCheck 162 KData.m6aT.toList KData.m6bT.toList eqs6 neqs6 = true := by
  decide +kernel

end CFSG.KC.Eight89K

end
