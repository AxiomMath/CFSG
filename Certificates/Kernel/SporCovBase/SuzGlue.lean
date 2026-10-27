module

public import Certificates.Kernel.SporCovBase.Suz
public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import Certificates.Kernel.Sporadic.SuzK.Keys
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.KD.SporCovBase.Suz

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.KS.PEnum
open CFSG.Sporadic.Suz (J a b)
open CertificateChecks.KernelSpor.SuzK (AL BE)


theorem hA : ∀ x < 22880, r32 AL x = idx 22880 a x := fun x hx => by
  have h := CFSG.Sporadic.Suz.rep_alpha x hx
  unfold CFSG.Sporadic.Suz.orb at h
  rw [CertificateChecks.KernelSpor.SuzK.orbitData_eq] at h
  change CFSG.Sporadic.Th.Native.ap (CertificateChecks.KernelSpor.SuzK.tabOf AL) x = _ at h
  rwa [CertificateChecks.KernelSpor.SuzK.ap_tabOf AL hx] at h

theorem hB : ∀ x < 22880, r32 BE x = idx 22880 b x := fun x hx => by
  have h := CFSG.Sporadic.Suz.rep_beta x hx
  unfold CFSG.Sporadic.Suz.orb at h
  rw [CertificateChecks.KernelSpor.SuzK.orbitData_eq] at h
  change CFSG.Sporadic.Th.Native.ap (CertificateChecks.KernelSpor.SuzK.tabOf BE) x = _ at h
  rwa [CertificateChecks.KernelSpor.SuzK.ap_tabOf BE hx] at h

theorem hAi : ∀ x < 22880, r32 AL x = idx 22880 a⁻¹ x :=
  inv_of_left hA fun _ hx => CertificateChecks.KernelSpor.SuzK.alpha_inv hx

theorem hBi : ∀ x < 22880, fBi x = idx 22880 b⁻¹ x :=
  inv_of_left hB fun _ hx => CertificateChecks.KernelSpor.SuzK.beta_ord hx

theorem bs_lt : ∀ x ∈ bs, x < 22880 := by decide

theorem sep_bs (g : J) (h : ∀ x ∈ bs, idx 22880 g x = x) : g = 1 := by
  apply CFSG.Sporadic.Suz.sep g
  intro t ht
  have hs : CFSG.Sporadic.Suz.Native.chainQ.size = 6 := rfl
  rw [hs] at ht
  interval_cases t <;> exact h _ (by decide)

theorem model : Model letP E (wE (fP a b)) ∧
    ∀ u, chW letP u = true → wE (fP a b) u = 1 → E u [] = true :=
  eqB_model hA hAi hB hBi bs_lt sep_bs

theorem factorization_five : (448345497600 : ℕ).factorization 5 = 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def _ Nat.prime_five]
  have h : padicValNat 5 17933819904 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (448345497600 : ℕ) = 5 * (5 * 17933819904) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem sporKRestCover_five_J : SporKRestCover 5 ↥J := by
  obtain ⟨hM, hc⟩ := model
  have hk := Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨hH, hL⟩, hs⟩, hS⟩, hne⟩, ht⟩ := hk
  have hMc : chA letP F.M = true := (hM.clH_facts hH ht).2.1
  have hR : ∀ k, wE (fP a b) (nthW F.R k) ∈ Subgroup.closure
      ((Subgroup.centralizer {wE (fP a b) F.Y1} : Set J) ∪
        Subgroup.centralizer {wE (fP a b) F.Y2}) :=
    hM.mem_of_stages (hM.mem_of_cl_letters hH ht hL) hMc hs hS
  refine hM.cover_of_cl Nat.prime_five
    (by rw [CFSG.Sporadic.Suz.card_J, factorization_five]) hc hH ht hne ?_
  rw [eq_top_iff, ← CFSG.Sporadic.Suz.closure_ab, Subgroup.closure_le]
  have e0 : nthW F.R 0 = [0] := rfl
  have e1 : nthW F.R 1 = [2] := rfl
  have h0 := hR 0
  have h1 := hR 1
  rw [e0, wE_cons, wE_nil, one_mul, fP_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fP_two] at h1
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

end CFSG.KD.SporCovBase.Suz

end
