module

public import Certificates.Data.Kernel.PermCent.OuterRepC
public import Certificates.Data.Kernel.PermCent.SylowListC
public import CFSG.GH74.KGroups.L33TablesInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33R.KOut

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV.SylL CFSG.Certificates.Kernel.PkCV.OutR

@[expose] noncomputable def gP : List (CV 26) := [cOf PA, cOf PB]

@[expose] noncomputable def gA3 : List (CV 26) := [cOf PA, cOf PB, cOf sg0]

@[expose] noncomputable def gS : List (CV 26) := [cOf sR, cOf sT]

@[expose] noncomputable def tO : CV 26 := cOf sg0 ^ 3

@[expose] def csOW : List (List Nat) :=
  [[1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]]

@[expose] noncomputable def csO : List (CV 26) := csOW.map (wordC gP)

@[expose] def csIW : List (List Nat) :=
  [[1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1]]

@[expose] noncomputable def csI : List (CV 26) := csIW.map (wordC gP)

@[expose] noncomputable def phi : CV 26 := wordC gA3 [1, 0, 1, 2, 2, 2, 1, 0, 1, 0, 1]

@[expose] noncomputable def phiPows : List (CV 26) := (List.range 8).map (phi ^ ·)

@[expose] noncomputable def bl : CV 26 := wordC gP [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] noncomputable def bc₁ : CV 26 :=
  wordC gP [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]

@[expose] noncomputable def bc₂ : CV 26 :=
  wordC gP [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

@[expose] noncomputable def wa : CV 26 := wordC gP [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]

@[expose] noncomputable def wb : CV 26 := wordC gP [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] noncomputable def refs : List (CV 26) := [wa]

theorem kPass : passA (elemsC QA) (elemsC QS) gS csO csI phiPows tO (cOf PA) = true := by
  decide +kernel

theorem kSubO : sub3C csO tO = true := by decide +kernel

theorem kSubI : sub3C csI (cOf PA) = true := by decide +kernel

theorem kBang : bangC tO bl bc₁ bc₂ = true := by decide +kernel

theorem kWord : wordWC (cOf s0) wa wb = true := by decide +kernel

theorem kConj4 : conj4C (elemsC QS) refs = true := by decide +kernel

theorem kOut : siftC QP tO 0 = false := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.L33R.KOut

end
