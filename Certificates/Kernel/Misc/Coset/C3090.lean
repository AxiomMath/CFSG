module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCardInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XC3V
public import Certificates.Kernel.Misc.Coset.XC3V1
public import Certificates.Kernel.Misc.Coset.XC3V2
public import Certificates.Kernel.Misc.Coset.XC3Vw

public section

namespace CertificateChecks.KernelMiscCoset.C3090

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.EvenSmallLie.SympSix.Co3Ident

theorem relsV_eq : relsV.map encW = CFSG.KBRoute.XC3V.rels := by decide +kernel
theorem relsV1_eq : relsV1.map encW = CFSG.KBRoute.XC3V1.rels := by decide +kernel
theorem relsV2_eq : relsV2.map encW = CFSG.KBRoute.XC3V2.rels := by decide +kernel
theorem relsVw_eq : relsVw.map encW = CFSG.KBRoute.XC3Vw.rels := by decide +kernel

theorem v0 : (genSub {r | r ∈ relsV.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).FiniteIndex ∧
    (genSub {r | r ∈ relsV.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).index ≤ 170775 := by
  have h1 := XC3V.t1
  unfold CFSG.KBRoute.XC3V.T1.ok at h1
  exact genSub_index_le_of_tableOk relsV relsV_eq h1 (by norm_num) CFSG.KBRoute.XC3V.top _
    (by decide +kernel)

theorem v1 : (genSub {r | r ∈ relsV1.map FreeGroup.mk} (subsetOf _ [0, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r | r ∈ relsV1.map FreeGroup.mk} (subsetOf _ [0, 2, 3, 4, 5])).index ≤ 7560 := by
  have h1 := XC3V1.t1
  unfold CFSG.KBRoute.XC3V1.T1.ok at h1
  exact genSub_index_le_of_tableOk relsV1 relsV1_eq h1 (by decide) CFSG.KBRoute.XC3V1.top _
    (by decide +kernel)

theorem v2 : Finite (PG _ relsV2) ∧ Nat.card (PG _ relsV2) ≤ 384 := by
  have h1 := XC3V2.t1
  unfold CFSG.KBRoute.XC3V2.T1.ok at h1
  exact card_le_of_tableOk relsV2 relsV2_eq h1 (by decide) CFSG.KBRoute.XC3V2.top rfl

theorem vw :
    (genSub {r | r ∈ relsVw.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).FiniteIndex ∧
    (genSub {r | r ∈ relsVw.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).index ≤ 1 := by
  have h1 := XC3Vw.t1
  unfold CFSG.KBRoute.XC3Vw.T1.ok at h1
  exact genSub_index_le_of_tableOk relsVw relsVw_eq h1 (by norm_num) CFSG.KBRoute.XC3Vw.top _
    (by decide +kernel)

end CertificateChecks.KernelMiscCoset.C3090

end
