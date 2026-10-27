module

public import Certificates.Kernel.SporCovBase.J2
public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import Certificates.Kernel.Sporadic.J2K.Final
public import CFSG.Sporadic.J2.Simple

public section

namespace CFSG.KD.SporCovBase.J2

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.KS.PEnum
open CFSG.Sporadic.J2 (J a b)
open CertificateChecks.KernelSpor.J2K (AL AI BE BI)


theorem hA : ∀ x < 315, r32 AL x = idx 315 a x := fun x hx => by
  have h := CFSG.Sporadic.J2.rep_alpha x hx
  unfold CFSG.Sporadic.J2.orb at h
  rwa [CertificateChecks.KernelSpor.J2K.orb_eq.1, CertificateChecks.KernelSpor.J2K.al_get hx] at h

theorem hB : ∀ x < 315, r32 BE x = idx 315 b x := fun x hx => by
  have h := CFSG.Sporadic.J2.rep_beta x hx
  unfold CFSG.Sporadic.J2.orb at h
  rwa [CertificateChecks.KernelSpor.J2K.orb_eq.1, CertificateChecks.KernelSpor.J2K.be_get hx] at h

theorem hAi : ∀ x < 315, r32 AI x = idx 315 a⁻¹ x :=
  inv_of_left hA fun _ hx => (CertificateChecks.KernelSpor.J2K.inv_facts hx).2.1

theorem hBi : ∀ x < 315, r32 BI x = idx 315 b⁻¹ x :=
  inv_of_left hB fun _ hx => (CertificateChecks.KernelSpor.J2K.inv_facts hx).2.2.2.1

theorem bs_lt : ∀ x ∈ bs, x < 315 := by decide

theorem sep_bs (g : J) (h : ∀ x ∈ bs, idx 315 g x = x) : g = 1 := by
  apply CFSG.Sporadic.J2.sep g
  intro t ht
  rw [CFSG.Sporadic.J2.chainQ_size] at ht
  interval_cases t <;> exact h _ (by decide)

theorem model : Model letP E (wE (fP a b)) ∧
    ∀ u, chW letP u = true → wE (fP a b) u = 1 → E u [] = true :=
  eqB_model hA hAi hB hBi bs_lt sep_bs

theorem card_J : Nat.card J = 604800 := by
  have h := CFSG.Sporadic.J2.card_lvl_zero
  rwa [CFSG.Sporadic.J2.lvl_zero, Subgroup.card_top] at h

theorem factorization_three : (604800 : ℕ).factorization 3 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 22400 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (604800 : ℕ) = 3 * (3 * (3 * 22400)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem factorization_five : (604800 : ℕ).factorization 5 = 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def _ Nat.prime_five]
  have h : padicValNat 5 24192 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (604800 : ℕ) = 5 * (5 * 24192) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem top_of_seeds {R : List (List ℕ)} (e0 : nthW R 0 = [0]) (e1 : nthW R 1 = [2])
    {T : Subgroup J} (h : ∀ k, wE (fP a b) (nthW R k) ∈ T) : T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  rw [e0, wE_cons, wE_nil, one_mul, fP_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fP_two] at h1
  rw [eq_top_iff, ← CFSG.Sporadic.J2.closure_ab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem sporKRestCover_three_J : SporKRestCover 3 ↥J := by
  obtain ⟨hM, hc⟩ := model
  exact hM.cover_of_p3l Nat.prime_three (by rw [card_J, factorization_three]) hc Ck.ok3
    fun _ => top_of_seeds rfl rfl

theorem sporKRestCover_five_J : SporKRestCover 5 ↥J := by
  obtain ⟨hM, hc⟩ := model
  have hk := Ck.ok5
  unfold chk5 at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨hH, hL⟩, hs⟩, hS⟩, hne⟩, ht⟩ := hk
  have hMc : chA letP F5.M = true := (hM.clH_facts hH ht).2.1
  refine hM.cover_of_cl Nat.prime_five (by rw [card_J, factorization_five]) hc hH ht hne ?_
  exact top_of_seeds rfl rfl (hM.mem_of_stages (hM.mem_of_cl_letters hH ht hL) hMc hs hS)

end CFSG.KD.SporCovBase.J2

end
