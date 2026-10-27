module

public import Certificates.Kernel.L34W.OutCov
public import Certificates.Kernel.L34W.Glue
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34W.OutCovSound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.L34W CFSG.KC.L34W.OCS CFSG.KC.L34K
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.GrS4.OutCov

theorem enum_parts {G : ℕ → ℕ} {k cnt : ℕ} {T PL POS SRT SRI : ℕ → ℕ}
    (h : ocE G k cnt T PL POS SRT SRI = true) :
    penumHdK (pidn 42 6) cnt 64 T PL = true ∧
      ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false G G k cnt T PL POS SRT SRI i = true := by
  unfold ocE at h
  rw [bAnd_iff] at h
  exact ⟨h.1, allN_spec h.2⟩

theorem case_c {c i k₁ k₂ m kk cnt : ℕ} {κ : ZMod 4 × ZMod 4} {G E PL POS SRT SRI : ℕ → ℕ}
    (he : ocE G kk cnt E PL POS SRT SRI = true) (hc : ocK c G kk E cnt = true) (hi : i < 36)
    (h0 : hf (OC.H c) 0 = 64 * i) (h1 : hf (OC.H c) 1 = k₁) (h2 : hf (OC.H c) 2 = k₂)
    (h3 : hf (OC.H c) 3 = m) (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) :
    (c3Case (indexOf (enumBFS 42 gensS 20160).tabs) (enumBFS 42 gensS 20160).tabs κ 0 i &&
      c4Case κ 0 i && c5Case κ 0 i) = true := by
  unfold ocK at hc
  exact case_sound t1Of alOf bounds_k gensG y_k L34Cert.hS.1 (enum_parts he).1 (enum_parts he).2 hi
    h0 h1 h2 h3 hκ hm hc

theorem invar_false {κ : ZMod 4 × ZMod 4} {k₁ k₂ m i : ℕ} (hi : i < 36)
    (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) (h : invK AlX.F k₁ k₂ m i = false) :
    invar κ i = false := by
  rw [invar_eq alOf hi hκ hm]
  exact h

theorem pair_ok {κ : ZMod 4 × ZMod 4} (hκ : κ ∈ kGensB) {r : ℕ} (hr : r < 3)
    (hinv : invar κ (r + 1) = true) :
    (c3Case (indexOf (enumBFS 42 gensS 20160).tabs) (enumBFS 42 gensS 20160).tabs κ 0 (r + 1) &&
      c4Case κ 0 (r + 1) && c5Case κ 0 (r + 1)) = true := by
  simp only [kGensB, List.mem_cons, List.not_mem_nil, or_false] at hκ
  rcases hκ with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases r
  · exact case_c (k₁ := 1) (k₂ := 0) (m := 4369) ch22971e_0 ch22971c_0 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact case_c (k₁ := 1) (k₂ := 0) (m := 4369) ch22971e_2 ch22971c_2 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact case_c (k₁ := 1) (k₂ := 0) (m := 4369) ch22971e_4 ch22971c_4 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact absurd hinv (by rw [invar_false (k₁ := 0) (k₂ := 1) (m := 15) (by norm_num) (by decide)
      (by decide +kernel) (by decide +kernel)]; decide)
  · exact absurd hinv (by rw [invar_false (k₁ := 0) (k₂ := 1) (m := 15) (by norm_num) (by decide)
      (by decide +kernel) (by decide +kernel)]; decide)
  · exact case_c (k₁ := 0) (k₂ := 1) (m := 15) ch22971e_5 ch22971c_5 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact absurd hinv (by rw [invar_false (k₁ := 1) (k₂ := 1) (m := 33825) (by norm_num)
      (by decide) (by decide +kernel) (by decide +kernel)]; decide)
  · exact absurd hinv (by rw [invar_false (k₁ := 1) (k₂ := 1) (m := 33825) (by norm_num)
      (by decide) (by decide +kernel) (by decide +kernel)]; decide)
  · exact case_c (k₁ := 1) (k₂ := 1) (m := 33825) ch22971e_6 ch22971c_6 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact case_c (k₁ := 1) (k₂ := 2) (m := 16705) ch22971e_0 ch22971c_1 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact case_c (k₁ := 1) (k₂ := 2) (m := 16705) ch22971e_2 ch22971c_3 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact case_c (k₁ := 1) (k₂ := 2) (m := 16705) ch22971e_4 ch22971c_7 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact absurd hinv (by rw [invar_false (k₁ := 2) (k₂ := 1) (m := 2565) (by norm_num)
      (by decide) (by decide +kernel) (by decide +kernel)]; decide)
  · exact absurd hinv (by rw [invar_false (k₁ := 2) (k₂ := 1) (m := 2565) (by norm_num)
      (by decide) (by decide +kernel) (by decide +kernel)]; decide)
  · exact case_c (k₁ := 2) (k₂ := 1) (m := 2565) ch22971e_5 ch22971c_8 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)
  · exact absurd hinv (by rw [invar_false (k₁ := 1) (k₂ := 3) (m := 9345) (by norm_num)
      (by decide) (by decide +kernel) (by decide +kernel)]; decide)
  · exact absurd hinv (by rw [invar_false (k₁ := 1) (k₂ := 3) (m := 9345) (by norm_num)
      (by decide) (by decide +kernel) (by decide +kernel)]; decide)
  · exact case_c (k₁ := 1) (k₂ := 3) (m := 9345) ch22971e_6 ch22971c_9 (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)

theorem rho_ok {κ : ZMod 4 × ZMod 4} (hκ : κ ∈ kGensB) {r : ℕ} (hr : r < 3) :
    (allBelow 64 fun t₀ => allBelow 36 fun i₀ =>
      !(rT t₀ i₀ == unpack 42 6 (RP (r + 1)) && invar κ i₀) ||
        (c3Case (indexOf (enumBFS 42 gensS 20160).tabs) (enumBFS 42 gensS 20160).tabs κ t₀ i₀ &&
          c4Case κ t₀ i₀ && c5Case κ t₀ i₀)) = true := by
  rw [allBelow_iff']
  intro t ht
  rw [allBelow_iff']
  intro i hi
  cases hmt : (rT t i == unpack 42 6 (RP (r + 1)))
  · rfl
  · obtain ⟨rfl, rfl⟩ := match_iff gensG y_k ch22971g_match hr (L34Cert.cnRP (by omega)) ht hi hmt
    cases hinv : invar κ (r + 1)
    · rfl
    · rw [Bool.and_self, Bool.not_true, Bool.false_or]
      exact pair_ok hκ hr hinv

theorem outCovOK_true : outCovOK = true := by
  unfold outCovOK
  dsimp only
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨invOKE_of t1Of ch22971g_inv, fun κ hκ => ?_⟩
  rw [List.all_eq_true]
  intro ρ hρ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl
  · rw [L34Cert.r2_eq]
    exact rho_ok hκ (r := 0) (by norm_num)
  · rw [L34Cert.r3_eq]
    exact rho_ok hκ (r := 1) (by norm_num)
  · rw [L34Cert.r4_eq]
    exact rho_ok hκ (r := 2) (by norm_num)

end CertificateChecks.KernelL34W

end
