
module

public import Certificates.Kernel.He7223.GlueNorm

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7223

open CFSG.KC.Enum CFSG.KS CFSG.KC.WordPts CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CertificateChecks.KernelLC.HeFix

theorem bBL_eq : bBL = bB := rfl

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem E_fix_bB :
    ∀ i < 6, ∀ p : Fin 8330, (p : ℕ) ∈ bB → elt (eW.getD i []) p = p := by
  intro i hi p hp
  rw [eW_eq]
  have h := allN_ct ch7223eB i hi
  have hl : ∀ wd ∈ [EB.getD i []], lettersOK gens3.length wd = true := by
    intro wd hw
    rw [List.mem_singleton] at hw
    subst hw
    exact letters3 EB_letters _ (getD_mem (lt_of_lt_of_eq hi (by decide +kernel)))
  have := fixPtsK_sound letRep_LU hl h p hp
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  exact this

theorem BB_cols : ∀ j < 3, ∀ i < 6, ∃ r < 6, CFSG.KLie.CT.bit (colF 6 (gen BB j) i) r = true := by
  decide +kernel

theorem lsGen_maps_bB :
    ∀ w ∈ lsGenW, ∀ p : Fin 8330, (p : ℕ) ∈ bB → ((elt w p : Fin 8330) : ℕ) ∈ bB := by
  have key : ∀ j < 3, permBK (lg j) (gen BB j) = true → ∀ p : Fin 8330, (p : ℕ) ∈ bB →
      ((elt (lg j) p : Fin 8330) : ℕ) ∈ bB := by
    intro j hj h p hp
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
    have hi6 : i < 6 := hi
    have h1 := allN_ct h i hi6
    unfold permBK at h1
    rw [strictB_eq'] at h1
    obtain ⟨r, hr, hb⟩ := BB_cols j hj i hi6
    have h2 := allN_ct h1 r hr
    rw [hb] at h2
    have h3 := Nat.eq_of_beq_eq_true h2
    have hev := evW_eq letRep_LU (lettersOK_mono (by rw [gens3_length]; norm_num)
      (LG_letters j hj)) p
    have hpi' : bBL.getD i 0 = (p : ℕ) := by
      rw [bBL_eq, List.getD_eq_getElem _ _ hi]
      exact hpi
    rw [hpi'] at h3
    have hv : ((elt (lg j) p : Fin 8330) : ℕ) = evW 8330 14 LU LUI (lg j) p := hev.symm
    rw [hv, h3, List.getD_eq_getElem _ _ (lt_of_lt_of_eq hr (by decide))]
    exact List.getElem_mem _
  obtain ⟨h0, h12⟩ := andB_true ch7223lB
  obtain ⟨h1, h2⟩ := andB_true h12
  rw [lsGenW_eq]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact key 0 (by norm_num) h0
  · exact key 1 (by norm_num) h1
  · exact key 2 (by norm_num) h2

end CertificateChecks.KernelHe7223

end
