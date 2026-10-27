module

public import Certificates.Kernel.HSMult.Tables
public import Certificates.Kernel.M23Mult.Bounds

public section

namespace CertificateChecks.KernelHSMult

open CFSG.Certificates CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.HSMultiplier
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

theorem rels5_eq : hsRels5.map encW = KernelM23Mult.rels5 := by decide +kernel

theorem cover5_eq : hsCover5.map encW = KernelM23Mult.cover5 := by decide +kernel

theorem words_eq : CFSG.KBRoute.HSMP2.T1.words =
    (subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)] := by decide +kernel

theorem wordsC_eq : CFSG.KBRoute.HSMC2.T1.words =
    (subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)] := by decide +kernel

theorem card_presented : Finite (PG 6 hsRels) ∧ Nat.card (PG 6 hsRels) ≤ 44352000 := by
  have h2 := p2
  unfold CFSG.KBRoute.HSMP2.T1.ok at h2
  have h1 := KernelM23Mult.p1
  unfold CFSG.KBRoute.M23MP1.T1.ok at h1
  obtain ⟨f, c⟩ := KernelM23Mult.card_le_of_tables hsRels h2 rfl CFSG.KBRoute.HSMP2.top words_eq h1
    rels5_eq CFSG.KBRoute.M23MP1.top rfl
  exact ⟨f, c.trans (by norm_num)⟩

theorem card_cover : Finite HSCover ∧ Nat.card HSCover ≤ 88704000 := by
  change Finite (PresentedGroup (coverRelators (wordSet hsRels) fun i => FreeGroup.mk (hsCommWord i))) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet hsRels) fun i => FreeGroup.mk (hsCommWord i))) ≤
      88704000
  rw [coverRelators_wordSet]
  have h2 := c2
  unfold CFSG.KBRoute.HSMC2.T1.ok at h2
  have h1 := KernelM23Mult.c1
  unfold CFSG.KBRoute.M23MC1.T1.ok at h1
  obtain ⟨f, c⟩ := KernelM23Mult.card_le_of_tables hsCover h2 rfl CFSG.KBRoute.HSMC2.top wordsC_eq h1
    cover5_eq CFSG.KBRoute.M23MC1.top rfl
  exact ⟨f, c.trans (by norm_num)⟩

end CertificateChecks.KernelHSMult

end
