module

public import CFSG.Timmesfeld.Exceptional.DeepAllNearInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XAN1
public import Certificates.Kernel.Misc.Coset.XAN2

public section

namespace CertificateChecks.KernelMiscCoset.C8053

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Timmesfeld.Moufang.Deep

theorem rels1_eq : (relsAN ++ [prodAN]).map encW = CFSG.KBRoute.XAN1.rels := by decide +kernel

theorem rels2_eq : (relsAN ++ [prodAN ++ [letAN 0 false]]).map encW = CFSG.KBRoute.XAN2.rels := by
  decide +kernel

theorem card_le : (Finite (PG 7 (relsAN ++ [prodAN])) ∧ Nat.card (PG 7 (relsAN ++ [prodAN])) ≤ 1) ∧
    (Finite (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) ∧
      Nat.card (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) ≤ 1) := by
  have h1 := XAN1.t1
  unfold CFSG.KBRoute.XAN1.T1.ok at h1
  have h2 := XAN2.t1
  unfold CFSG.KBRoute.XAN2.T1.ok at h2
  exact ⟨card_le_of_tableOk _ rels1_eq h1 (by norm_num) CFSG.KBRoute.XAN1.top rfl,
    card_le_of_tableOk _ rels2_eq h2 (by norm_num) CFSG.KBRoute.XAN2.top rfl⟩

end CertificateChecks.KernelMiscCoset.C8053

end
