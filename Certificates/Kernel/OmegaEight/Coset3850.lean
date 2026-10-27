module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain
public import Certificates.Kernel.Misc.Coset.XN28
public import Certificates.Kernel.Misc.Coset.XN27
public import Certificates.Kernel.Misc.Coset.XN16
public import Certificates.Kernel.Misc.Coset.XN5
public import Certificates.Kernel.Misc.Coset.XN4
public import Certificates.Kernel.Misc.Coset.XN3
public import Certificates.Kernel.Misc.Coset.XN2

public section

namespace CertificateChecks.KernelO8.C3850

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.EvenSmallLie.OmegaEight.NSplit

theorem relA1_card : Finite (PG _ relA1) ∧ Nat.card (PG _ relA1) ≤ 2 := by
  have h := CertificateChecks.KernelMiscCoset.XN2.t1
  unfold CFSG.KBRoute.XN2.T1.ok at h
  exact card_le_of_tableOk relA1 (by decide +kernel) h (by decide) CFSG.KBRoute.XN2.top rfl

theorem relA2_card : Finite (PG _ relA2) ∧ Nat.card (PG _ relA2) ≤ 3 * 2 := by
  have h := CertificateChecks.KernelMiscCoset.XN3.t1
  unfold CFSG.KBRoute.XN3.T1.ok at h
  exact card_le_of_index_restrict relA2 (subsetOf 2 [0])
    (genSub_index_le_of_tableOk relA2 (by decide +kernel) h (by decide) CFSG.KBRoute.XN3.top _
      (by decide +kernel)) relA1_card

theorem relA3_card : Finite (PG _ relA3) ∧ Nat.card (PG _ relA3) ≤ 4 * (3 * 2) := by
  have h := CertificateChecks.KernelMiscCoset.XN4.t1
  unfold CFSG.KBRoute.XN4.T1.ok at h
  exact card_le_of_index_restrict relA3 (subsetOf 3 [0, 1])
    (genSub_index_le_of_tableOk relA3 (by decide +kernel) h (by decide) CFSG.KBRoute.XN4.top _
      (by decide +kernel)) relA2_card

theorem relA4_card : Finite (PG _ relA4) ∧ Nat.card (PG _ relA4) ≤ 5 * (4 * (3 * 2)) := by
  have h := CertificateChecks.KernelMiscCoset.XN5.t1
  unfold CFSG.KBRoute.XN5.T1.ok at h
  exact card_le_of_index_restrict relA4 (subsetOf 4 [0, 1, 2])
    (genSub_index_le_of_tableOk relA4 (by decide +kernel) h (by decide) CFSG.KBRoute.XN5.top _
      (by decide +kernel)) relA3_card

theorem relD5_card : Finite (PG _ relD5) ∧ Nat.card (PG _ relD5) ≤ 16 * (5 * (4 * (3 * 2))) := by
  have h := CertificateChecks.KernelMiscCoset.XN16.t1
  unfold CFSG.KBRoute.XN16.T1.ok at h
  exact card_le_of_index_restrict relD5 (subsetOf 5 [1, 2, 3, 4])
    (genSub_index_le_of_tableOk relD5 (by decide +kernel) h (by decide) CFSG.KBRoute.XN16.top _
      (by decide +kernel)) relA4_card

theorem relE6_card :
    Finite (PG _ relE6) ∧ Nat.card (PG _ relE6) ≤ 27 * (16 * (5 * (4 * (3 * 2)))) := by
  have h := CertificateChecks.KernelMiscCoset.XN27.t1
  unfold CFSG.KBRoute.XN27.T1.ok at h
  exact card_le_of_index_restrict relE6 (subsetOf 6 [1, 2, 3, 4, 5])
    (genSub_index_le_of_tableOk relE6 (by decide +kernel) h (by decide) CFSG.KBRoute.XN27.top _
      (by decide +kernel)) relD5_card

theorem cosetCard3850 : Finite (PG 7 relPG) ∧ Nat.card (PG 7 relPG) ≤ 1451520 := by
  have h := CertificateChecks.KernelMiscCoset.XN28.t1
  unfold CFSG.KBRoute.XN28.T1.ok at h
  exact card_le_of_index_restrict relPG (subsetOf 7 [0, 1, 2, 3, 4, 5])
    (genSub_index_le_of_tableOk relPG (by decide +kernel) h (by decide) CFSG.KBRoute.XN28.top _
      (by decide +kernel)) relE6_card

end CertificateChecks.KernelO8.C3850

end
