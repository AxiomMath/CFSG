module

public import Certificates.Data.Kernel.PermCent.SylowListC
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33R.KSyl

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV.SylL

@[expose] noncomputable def gA : List (CV 26) := [cOf PA, cOf PB, cOf sg0]

@[expose] def tGenW : List (List Nat) :=
  [[1, 2, 1, 2, 0, 1], [1, 1, 2, 1, 1, 0, 2, 1], [2, 1, 1, 2, 0, 1, 2, 1]]

@[expose] noncomputable def tGens : List (CV 26) := tGenW.map (wordC gA)

@[expose] def tEltW : List (List Nat) :=
  [[], [0], [1], [2], [1, 0], [2, 0], [0, 1], [1, 1], [2, 1], [0, 2], [1, 2], [0, 1, 0], [1, 1, 0],
    [2, 1, 0], [0, 2, 0], [1, 2, 0], [1, 0, 1], [2, 0, 1], [1, 1, 1], [2, 1, 1], [1, 0, 2],
    [2, 0, 2], [1, 0, 1, 0], [2, 0, 1, 0], [1, 1, 1, 0], [2, 1, 1, 0], [1, 0, 2, 0], [2, 0, 2, 0],
    [1, 1, 0, 1], [2, 1, 0, 1], [1, 1, 0, 1, 0], [2, 1, 0, 1, 0]]

@[expose] noncomputable def tElts : List (CV 26) := tEltW.map (wordC tGens)

@[expose] noncomputable def reps : List (CV 26) := [cOf PA, cOf sg0 ^ 3]

@[expose] def covW : List (Option (Nat × List Nat)) :=
  [none, some (0, [2, 2, 2, 2]), none, some (1, [1, 1, 2, 1, 1]), none, none, none, some (0, []),
    some (1, [0, 1, 2, 2, 1, 0, 1, 1]), none, some (1, [1, 2, 1, 0, 2]), none, some (0, [2, 2]),
    some (1, [1, 0, 1, 0, 2]), some (1, [0, 2, 0, 2, 0, 1]), some (1, [1, 0, 2, 1]),
    some (0, [2, 1, 1, 0, 2]), some (1, [1, 1, 0, 1, 0, 1]), none, some (1, [1, 2, 2]),
    some (1, [0, 1, 1, 2]), some (0, [1, 1, 2, 0, 1, 0, 1]), none, none, none, none, none, none,
    none, none, none, some (1, [1, 0, 2, 2])]

theorem kLen : tElts.length = 32 := rfl

theorem kClosed : closedC tGens tElts = true := by decide +kernel

theorem kCover : coverC gA reps tElts covW = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.L33R.KSyl

end
