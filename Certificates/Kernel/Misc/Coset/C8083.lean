module

public import CFSG.Quasithin.Recognition.M12AscCoxInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XCox5

public section

namespace CertificateChecks.KernelMiscCoset.C8083

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Quasithin

theorem rels_eq : (coxRels 5).map encW = CFSG.KBRoute.XCox5.rels := by decide +kernel

theorem card_le : Finite (PG 5 (coxRels 5)) ∧ Nat.card (PG 5 (coxRels 5)) ≤ 720 := by
  have h1 := XCox5.t1
  unfold CFSG.KBRoute.XCox5.T1.ok at h1
  have h := index_le_of_tableOk (coxRels 5) rels_eq h1 (by norm_num) CFSG.KBRoute.XCox5.top
  rw [show CFSG.KBRoute.XCox5.T1.words = [] from rfl] at h
  exact card_le_of_index_bot _ h

end CertificateChecks.KernelMiscCoset.C8083

end
