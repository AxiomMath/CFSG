module

public import CFSG.Quasithin.Recognition.M12AscHModelInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XAscH

public section

namespace CertificateChecks.KernelMiscCoset.C8084

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Quasithin

theorem rels_eq : ascHRels.map encW = CFSG.KBRoute.XAscH.rels := by decide +kernel

theorem card_le : Finite (PG 4 ascHRels) ∧ Nat.card (PG 4 ascHRels) ≤ 192 := by
  have h1 := XAscH.t1
  unfold CFSG.KBRoute.XAscH.T1.ok at h1
  exact card_le_of_tableOk ascHRels rels_eq h1 (by norm_num) CFSG.KBRoute.XAscH.top rfl

end CertificateChecks.KernelMiscCoset.C8084

end
