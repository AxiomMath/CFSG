module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XS6R
public import Certificates.Kernel.Misc.Coset.XS6Y
public import Certificates.Kernel.Misc.Coset.XS6C
public import Certificates.Kernel.Misc.Coset.XS6C1

public section

namespace CertificateChecks.KernelMiscCoset.C3008

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.EvenSmallLie.SympSix CFSG.LieType.Multipliers

set_option maxRecDepth 100000 in
theorem model : ((rels.all fun r => decide (wordPerm r = 1)) && ((List.finRange 3).all fun i =>
    decide (wordPerm (commWords (coverPairs i)) = sympGen i)) && decide (wordPerm wordSB =
    CFSG.EvenSmallLie.Sp6.sp6B)) = true := by
  decide +kernel

theorem rels_eq : rels.map encW = CFSG.KBRoute.XS6R.rels := by decide +kernel
theorem relsY_eq : relsY.map encW = CFSG.KBRoute.XS6Y.rels := by decide +kernel
theorem coverWs_eq : coverWs.map encW = CFSG.KBRoute.XS6C.rels := by decide +kernel
theorem cover₁_eq : cover₁.map encW = CFSG.KBRoute.XS6C1.rels := by decide +kernel

theorem pres : (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
    (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 56 := by
  have h1 := XS6R.t1
  unfold CFSG.KBRoute.XS6R.T1.ok at h1
  exact genSub_index_le_of_tableOk rels rels_eq h1 (by decide) CFSG.KBRoute.XS6R.top _
    (by decide +kernel)

theorem presY : (Subgroup.zpowers (PresentedGroup.mk {r | r ∈ relsY.map FreeGroup.mk}
      (FreeGroup.mk [(1, true)]))).FiniteIndex ∧
    (Subgroup.zpowers (PresentedGroup.mk {r | r ∈ relsY.map FreeGroup.mk}
      (FreeGroup.mk [(1, true)]))).index ≤ 5184 := by
  have h1 := XS6Y.t1
  unfold CFSG.KBRoute.XS6Y.T1.ok at h1
  exact zpowers_index_le_of_tableOk relsY relsY_eq h1 (by decide) CFSG.KBRoute.XS6Y.top _
    (by decide +kernel)

theorem cover : (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
    (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 56 := by
  have h1 := XS6C.t1
  unfold CFSG.KBRoute.XS6C.T1.ok at h1
  exact genSub_index_le_of_tableOk coverWs coverWs_eq h1 (by decide) CFSG.KBRoute.XS6C.top _
    (by decide +kernel)

theorem cover₁_card : Finite (PG _ cover₁) ∧ Nat.card (PG _ cover₁) ≤ 51840 := by
  have h1 := XS6C1.t1
  unfold CFSG.KBRoute.XS6C1.T1.ok at h1
  exact card_le_of_tableOk cover₁ cover₁_eq h1 (by decide) CFSG.KBRoute.XS6C1.top rfl

end CertificateChecks.KernelMiscCoset.C3008

end
