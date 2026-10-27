module

public import Certificates.Data.Kernel.PermCent.OuterRepOC
public import Certificates.Data.Kernel.PermCent.SylowListC
public import CFSG.GH74.KGroups.U33TablesInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33R.KOut

open CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV.SylL CFSG.Certificates.Kernel.PkCV.OutR

@[expose] noncomputable def gP : List (CV 28) := [cOf pa, cOf pb]

@[expose] noncomputable def gS : List (CV 28) := [cOf sy0, cOf sy1, cOf sy2, cOf sy3, cOf sy4]

@[expose] noncomputable def tO : CV 28 := cOf pt2

@[expose] noncomputable def tI : CV 28 := cOf pu

@[expose] noncomputable def inP (x : CV 28) : Bool := siftC QP x 0

@[expose] def csOW : List (List Nat) :=
  [[1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]]

@[expose] noncomputable def csO : List (CV 28) := csOW.map (wordC gP)

@[expose] def csIW : List (List Nat) := [[0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]]

@[expose] noncomputable def csI : List (CV 28) := csIW.map (wordC gP)

@[expose] noncomputable def bl : CV 28 := wordC gP [1, 0, 1, 0, 1, 0, 1, 1, 0, 0]

@[expose] noncomputable def bc₁ : CV 28 := wordC gP [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] noncomputable def bc₂ : CV 28 := wordC gP [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]

@[expose] noncomputable def wa : CV 28 := wordC gP [1]

@[expose] noncomputable def wb : CV 28 := wordC gP [0, 0, 1, 1, 0]

@[expose] noncomputable def e3 : CV 28 := wordC gP [0, 1, 0, 0]

@[expose] def refsW : List (List Nat) :=
  [[1], [1, 1, 0, 1, 0, 0, 1], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]]

@[expose] noncomputable def refs : List (CV 28) := refsW.map (wordC gP)

@[expose] def ksW : List (List Nat) := [[], [1, 0, 1, 0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 1, 0, 0]]

@[expose] noncomputable def ks : List (CV 28) := ksW.map (wordC gP)

theorem kPass : passO inP (elemsC QA) (elemsC QS) gS csO csI tO tI = true := by
  decide +kernel

theorem kSubO : sub3C csO tO = true := by decide +kernel

theorem kSubI : sub3C csI tI = true := by decide +kernel

theorem kBang : bangC tO bl bc₁ bc₂ = true := by decide +kernel

theorem kWord : wordWC (cOf s0) wa wb = true := by decide +kernel

theorem kConj4 : conj4KC (elemsC QS) refs ks = true := by decide +kernel

theorem kE3 : inP (cOf t0) = true ∧ powOneC (cOf t0) 2 = true ∧ decide (cOf t0 = 1) = false ∧
    powOneC e3 3 = true ∧ decide (e3 = 1) = false ∧ eq22C e3 (cOf t0) (cOf t0) e3 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem kOut : inP tO = false ∧ inP tI = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.U33R.KOut

end
