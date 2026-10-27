module

public import Certificates.Kernel.K36K.J2.Checks
public import Certificates.Kernel.CoreD2K.J2.Glue
public import CFSG.Certificates.Kernel.K36K.Planes

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK36K.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MaxD2 CFSG.KD.K36K
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LocalAnalysis.UniquenessCase.UCK.Spor
  Certificates.K36Spor
open CertificateChecks.KernelCoreD2K.J2 (k_sz tab0 tab1)

theorem hyps3 : PHyps 315 9 j2SData3 CertificateChecks.KernelCoreD2K.J2.GP
    CertificateChecks.KernelCoreD2K.J2.GPI GT3 GTI3 RE3.G RE3.GI RE3.T RE3.PL RE3.POS RE3.SRT
    RE3.SRI RE3.cnt 27 27 where
  hn := k_sz
  hgens := k3_gens
  hh := k3_eh
  hsl := by
    rw [← Nat.eq_of_beq_eq_true k3_ek]
    exact k3_esl
  hlen := by rw [Nat.eq_of_beq_eq_true k3_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true k3_ecnt]
    rfl
  hnab := k3_nab
  hcen := k3_cen
  hlines := k3_lines
  hcent := k3_cent
  hwords := k3_words
  hgen := by decide

theorem planes_j2P_three : ∃ E : Subgroup ↥j2P, Nat.card E = 27 ∧
    ∀ A : Subgroup ↥j2P, A ≤ E → CFSG.Open.IsElemAbelian 3 A → Nat.card A = 9 →
      Subgroup.closure (centSet A) = ⊤ := by
  obtain ⟨E, hEc, hEG, hE⟩ := planes_three hyps3 Nat.prime_three tab0 tab1
  obtain ⟨E', hE'c, hE'⟩ := closure_centSet_eq_top (G := j2P) rfl ⟨E, hEc, hEG, hE⟩
  exact ⟨E', hE'c.trans (by decide), fun A hAE hAe hAc =>
    hE' A hAE hAe (hAc.trans (by decide))⟩

theorem planes_j2P_five : ∃ E : Subgroup ↥j2P, Nat.card E = 25 ∧
    ∀ A : Subgroup ↥j2P, A ≤ E → CFSG.Open.IsElemAbelian 5 A → Nat.card A = 25 →
      Subgroup.closure (centSet A) = ⊤ := by
  obtain ⟨E, hEc, hEG, hE⟩ := planes_two k_sz k5_gens k5_cen (by decide) k5_v k5_cent k5_words
    ⟨0, by decide, rfl⟩ (by norm_num : Nat.Prime 5) tab0 tab1
  obtain ⟨E', hE'c, hE'⟩ := closure_centSet_eq_top (G := j2P) rfl
    ⟨E, hEc, hEG, fun A hAE _ hAc => hE A hAE hAc⟩
  exact ⟨E', hE'c.trans (by decide), fun A hAE hAe hAc =>
    hE' A hAE hAe (hAc.trans (by decide))⟩

end CertificateChecks.KernelK36K.J2

end
