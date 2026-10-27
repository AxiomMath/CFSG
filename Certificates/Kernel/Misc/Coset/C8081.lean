module

public import CFSG.Quasithin.Recognition.CertU33PresInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.CosetTableColumns
public import Certificates.Kernel.Misc.Coset.XU33a
public import Certificates.Kernel.Misc.Coset.XU33b

public section

namespace CertificateChecks.KernelMiscCoset.C8081

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Quasithin

theorem relsA_eq : u33PresRels.map encW = CFSG.KBRoute.XU33a.rels := by decide +kernel

theorem relsB_eq : u33PresRelsA.map encW = CFSG.KBRoute.XU33b.rels := by decide +kernel

theorem wordsA_eq : CFSG.KBRoute.XU33a.T1.words =
    (subsetOf 5 [0, 1, 2, 3]).map fun x => [(x.val, true)] := by decide +kernel

theorem card_le : Finite (PG 5 u33PresRels) ∧ Nat.card (PG 5 u33PresRels) ≤ 6048 := by
  have hb := XU33b.t1
  unfold CFSG.KBRoute.XU33b.T1.ok at hb
  obtain ⟨f1, c1⟩ := card_le_of_tableOk u33PresRelsA relsB_eq hb (by decide)
    CFSG.KBRoute.XU33b.top rfl
  have ha := XU33a.t1
  unfold CFSG.KBRoute.XU33a.T1.ok at ha
  obtain ⟨hfi, hidx⟩ := genSub_index_le_of_tableOk u33PresRels relsA_eq ha (by norm_num)
    CFSG.KBRoute.XU33a.top _ wordsA_eq
  obtain ⟨f0, c0⟩ := card_le_of_genSub_index u33PresRels (subsetOf 5 [0, 1, 2, 3]) hfi hidx
  exact ⟨f0, (c0.trans (Nat.mul_le_mul_left 63 c1)).trans (by norm_num)⟩

end CertificateChecks.KernelMiscCoset.C8081

end
