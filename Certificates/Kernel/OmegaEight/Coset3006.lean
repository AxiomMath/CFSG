module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XO8R
public import Certificates.Kernel.Misc.Coset.XO8C

public section

namespace CertificateChecks.KernelO8.C3006

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.EvenSmallLie.OmegaEight.Cover

theorem pres3006 : (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
    (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 120 := by
  have h := CertificateChecks.KernelMiscCoset.XO8R.t1
  unfold CFSG.KBRoute.XO8R.T1.ok at h
  exact genSub_index_le_of_tableOk rels (by decide +kernel) h (by decide) CFSG.KBRoute.XO8R.top _
    (by decide +kernel)

theorem cover3006 :
    (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
      (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 240 := by
  have h := CertificateChecks.KernelMiscCoset.XO8C.t1
  unfold CFSG.KBRoute.XO8C.T1.ok at h
  exact genSub_index_le_of_tableOk coverWs (by decide +kernel) h (by decide) CFSG.KBRoute.XO8C.top _
    (by decide +kernel)

end CertificateChecks.KernelO8.C3006

end
