module

public import Certificates.Kernel.SporCovBase.ON
public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Certificates.Kernel.SporCov.CensusSound
public import Certificates.Kernel.Sporadic.ON2.Final
public import CFSG.Sporadic.ON.Chain

public section

namespace CFSG.KD.SporCovBase.ON

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.KS.ON CertificateChecks.KernelSpor
open CFSG.Sporadic.ON (J ga gb)

theorem alpha_ap {x : ℕ} (hx : x < 245520) :
    CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.ON.Native.orbitData ()).alpha x = tab ONW.A x :=
  ((ON2.natTab_TR (ON2.orb_tabs ON2.mvAll ON2.ordAll ON2.sortAll).1
    fun i hi => (ON2.inv_facts ON2.invAll hi).1).2 x hx).1

theorem beta_ap {x : ℕ} (hx : x < 245520) :
    CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.ON.Native.orbitData ()).beta x = tab ONW.B x :=
  ((ON2.natTab_TR (ON2.orb_tabs ON2.mvAll ON2.ordAll ON2.sortAll).2
    fun i hi => (ON2.inv_facts ON2.invAll hi).2.1).2 x hx).1


theorem hA : ∀ x < 245520, tab ONW.A x = idx 245520 ga x := fun x hx => by
  have h := CFSG.Sporadic.ON.rep_ga x hx
  rwa [alpha_ap hx] at h

theorem hB : ∀ x < 245520, tab ONW.B x = idx 245520 gb x := fun x hx => by
  have h := CFSG.Sporadic.ON.rep_gb x hx
  rwa [beta_ap hx] at h

theorem hAi : ∀ x < 245520, tab ONW.U0 x = idx 245520 ga⁻¹ x :=
  inv_of_left hA fun _ hx => (ON2.inv_facts ON2.invAll hx).2.2.2.2.1

theorem hBi : ∀ x < 245520, tab ONW.U1 x = idx 245520 gb⁻¹ x :=
  inv_of_left hB fun _ hx => (ON2.inv_facts ON2.invAll hx).2.2.2.2.2.1

theorem bs_lt : ∀ x ∈ bs, x < 245520 := by decide

theorem sep_bs (g : J) (h : ∀ x ∈ bs, idx 245520 g x = x) : g = 1 := by
  have hl : ∀ i ≤ 3, g ∈ CFSG.Sporadic.ON.lvl i := by
    intro i hi
    induction i with
    | zero => exact CFSG.Sporadic.ON.mem_lvl_zero g
    | succ i ih =>
      refine (CFSG.Sporadic.ON.chain_facts'.2.1 i
        (by rw [CFSG.Sporadic.ON.chainBase_size]; omega) g (ih (by omega))).1 (h _ ?_)
      have hi3 : i < 3 := by omega
      interval_cases i <;> decide
  have hc := CFSG.Sporadic.ON.chain_facts'.2.2 3 (by rw [CFSG.Sporadic.ON.chainBase_size])
  rw [CFSG.Sporadic.ON.chainBase_size, Finset.Ico_self, Finset.prod_empty] at hc
  have hb := Subgroup.eq_bot_of_card_eq _ hc
  have hg := hl 3 le_rfl
  rw [hb] at hg
  exact (Subgroup.mem_bot).1 hg

theorem model : Model letP E (wE (fP ga gb)) ∧
    ∀ u, chW letP u = true → wE (fP ga gb) u = 1 → E u [] = true :=
  eqB_model hA hAi hB hBi bs_lt sep_bs

theorem key_eq (u v : List ℕ) (h : wE (fP ga gb) u = wE (fP ga gb) v) : Kf u = Kf v := by
  have hx : F3.X0 < 245520 := by decide
  unfold Kf
  rw [imB_eq hA hAi hB hBi u hx, imB_eq hA hAi hB hBi v hx, h]

theorem factorization_three : (460815505920 : ℕ).factorization 3 = 4 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 5689080320 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (460815505920 : ℕ) = 3 * (3 * (3 * (3 * 5689080320))) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem factorization_seven : (460815505920 : ℕ).factorization 7 = 3 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num : Nat.Prime 7)]
  have h : padicValNat 7 1343485440 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (460815505920 : ℕ) = 7 * (7 * (7 * 1343485440)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem top_of_seeds {R : List (List ℕ)} (e0 : nthW R 0 = [0]) (e1 : nthW R 1 = [2])
    {T : Subgroup J} (h : ∀ k, wE (fP ga gb) (nthW R k) ∈ T) : T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  rw [e0, wE_cons, wE_nil, one_mul, fP_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fP_two] at h1
  rw [eq_top_iff, ← CFSG.Sporadic.ON.closure_gab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem sporKRestCover_three_J : SporKRestCover 3 ↥J := by
  obtain ⟨hM, hc⟩ := model
  have hk := Ck.ok3
  unfold chk3 at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc, hH⟩, hI⟩, hT⟩, hpcl⟩, o₁⟩, o₂⟩, hcm⟩, h₁⟩, h₂⟩ := hk
  have hR : P3Rel 3 (wE (fP ga gb) F3.G1) (wE (fP ga gb) F3.G2) 1 :=
    ⟨one_pow 3, by rw [one_mul, mul_one], by rw [one_mul, mul_one],
      by rw [one_mul]; exact hM.comm o₁ o₂ hcm, ⟨0, by rw [pow_zero]; exact hM.pow o₁ h₁⟩,
      ⟨0, by rw [pow_zero]; exact hM.pow o₂ h₂⟩⟩
  obtain ⟨-, hgen⟩ := hM.generating_of_pclOK Nat.prime_three hR.isPGroup o₁ o₂ hpcl
    fun _ => top_of_seeds rfl rfl
  have hpc' : ∀ i < 4, ∀ j < 4, i ≤ j → pcR E 3 F3.S F3.Q 4 i j = true := by
    intro i hi j hj hij
    unfold pc3 at hpc
    have h := (allLt_iff _ 4).1 ((allLt_iff _ 4).1 hpc i hi) j hj
    have hb : Nat.blt j i = false := by
      rw [Bool.eq_false_iff]
      intro hb
      exact absurd (lt_of_blt hb) (by omega)
    rwa [hb, Bool.false_or] at h
  refine hM.cover_of_cen Nat.prime_three
    (by rw [CFSG.Sporadic.ON.card_J, factorization_three]) hc Kf
    (fun u v _ _ h => key_eq u v h) hpc' hH hI ((allLt_iff _ _).1 hT) ?_
  intro r hr
  rw [List.mem_singleton.1 hr]
  exact hgen

theorem sporKRestCover_seven_J : SporKRestCover 7 ↥J := by
  obtain ⟨hM, hc⟩ := model
  exact hM.cover_of_p3c (by norm_num)
    (by rw [CFSG.Sporadic.ON.card_J, factorization_seven]) hc Ck.ok7 fun _ => top_of_seeds rfl rfl

end CFSG.KD.SporCovBase.ON

end
