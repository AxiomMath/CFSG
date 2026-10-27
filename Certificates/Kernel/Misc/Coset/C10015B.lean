module

public import CFSG.LieType.Multipliers.U62BridgeInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain
public import Certificates.Kernel.Misc.Coset.XU62R0
public import Certificates.Kernel.Misc.Coset.XU62R1
public import Certificates.Kernel.Misc.Coset.XU62R2
public import Certificates.Kernel.Misc.Coset.XU62R3

public section

namespace CertificateChecks.KernelMiscCoset.C10015

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62

set_option maxRecDepth 100000

theorem t0 : rels.map encW = CFSG.KBRoute.XU62R0.rels := by decide +kernel
theorem t1 : rels₁.map encW = CFSG.KBRoute.XU62R1.rels := by decide +kernel
theorem t2 : rels₂.map encW = CFSG.KBRoute.XU62R2.rels := by decide +kernel
theorem t3 : rels₃.map encW = CFSG.KBRoute.XU62R3.rels := by decide +kernel
theorem w0 : CFSG.KBRoute.XU62R0.T1.words = (subsetOf 5 [0, 1, 2, 3]).map
    fun x => [(x.val, true)] := by decide +kernel
theorem w1 : CFSG.KBRoute.XU62R1.T1.words = (subsetOf (subsetOf 5 [0, 1, 2, 3]).length
    [0, 1, 2]).map fun x => [(x.val, true)] := by decide +kernel
theorem w2 : CFSG.KBRoute.XU62R2.T1.words = (subsetOf (subsetOf (subsetOf 5
    [0, 1, 2, 3]).length [0, 1, 2]).length [0, 1]).map fun x => [(x.val, true)] := by
  decide +kernel

theorem card_le₁ : Finite (PG (subsetOf 5 [0, 1, 2, 3]).length rels₁) ∧
    Nat.card (PG (subsetOf 5 [0, 1, 2, 3]).length rels₁) ≤ 13685760 := by
  have h1 := XU62R1.t1
  unfold CFSG.KBRoute.XU62R1.T1.ok at h1
  have h2 := XU62R2.t1
  unfold CFSG.KBRoute.XU62R2.T1.ok at h2
  have h3 := XU62R3.t1
  unfold CFSG.KBRoute.XU62R3.T1.ok at h3
  have c3 := card_le_of_tableOk rels₃ t3 h3 (by decide) CFSG.KBRoute.XU62R3.top rfl
  have c2 := card_le_of_index_restrict rels₂ _ (genSub_index_le_of_tableOk rels₂ t2 h2 (by decide)
    CFSG.KBRoute.XU62R2.top _ w2) c3
  have c1 := card_le_of_index_restrict rels₁ _ (genSub_index_le_of_tableOk rels₁ t1 h1 (by decide)
    CFSG.KBRoute.XU62R1.top _ w1) c2
  exact ⟨c1.1, c1.2.trans (by norm_num)⟩

theorem card_le : Finite (PG 5 rels) ∧ Nat.card (PG 5 rels) ≤ 9196830720 := by
  have h0 := XU62R0.t1
  unfold CFSG.KBRoute.XU62R0.T1.ok at h0
  have c0 := card_le_of_index_restrict rels _ (genSub_index_le_of_tableOk rels t0 h0 (by norm_num)
    CFSG.KBRoute.XU62R0.top _ w0) card_le₁
  exact ⟨c0.1, c0.2.trans (by norm_num)⟩

end CertificateChecks.KernelMiscCoset.C10015

end
