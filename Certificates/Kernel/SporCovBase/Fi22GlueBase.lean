
module

public import Certificates.Kernel.SporCovBase.Fi22
public import CFSG.Certificates.Kernel.SporCov.BaseFix
public import CFSG.Certificates.Kernel.SporCov.PCl
public import Certificates.Kernel.Fi22Core.OrbData
public import CFSG.Sporadic.Fi22.Simple

@[expose] public section

namespace CFSG.KD.SporCovBase.Fi22

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
open CFSG.Sporadic.Fi22 (J a b)

theorem hA : ∀ x < 3510, fA x = idx 3510 a x := fun x hx => by
  have h := CFSG.Sporadic.Fi22.rep_alpha x hx
  unfold CFSG.Sporadic.Fi22.orb at h
  rw [CertificateChecks.KernelFi22C.orbitData_eq] at h
  have e : CFSG.Sporadic.Fi22.Native.orbL.alpha = CFSG.Sporadic.Fi22.Native.orbTab 0 := rfl
  rwa [e, CFSG.KS.Fi22L.ap_orbTab hx] at h

theorem hB : ∀ x < 3510, fB x = idx 3510 b x := fun x hx => by
  have h := CFSG.Sporadic.Fi22.rep_beta x hx
  unfold CFSG.Sporadic.Fi22.orb at h
  rw [CertificateChecks.KernelFi22C.orbitData_eq] at h
  have e : CFSG.Sporadic.Fi22.Native.orbL.beta = CFSG.Sporadic.Fi22.Native.orbTab 1 := rfl
  rwa [e, CFSG.KS.Fi22L.ap_orbTab hx] at h

theorem hAi : ∀ x < 3510, fA x = idx 3510 a⁻¹ x := by
  rw [CFSG.Sporadic.Fi22.a_inv]
  exact hA

theorem okF_parts : (∀ x < 3510, fBi (fB x) = x) ∧ ∀ i < 4, chkT E i = true := by
  have h := Ck.okF
  unfold chkF at h
  rw [Bool.and_eq_true, allLt_iff] at h
  exact ⟨invB_spec h.1 (by norm_num), h.2⟩

theorem hBi : ∀ x < 3510, fBi x = idx 3510 b⁻¹ x :=
  inv_of_left hB okF_parts.1

theorem bs_lt : ∀ x ∈ bs, x < 3510 := by decide

theorem sep_bs (g : J) (h : ∀ x ∈ bs, idx 3510 g x = x) : g = 1 := by
  have hl : ∀ i ≤ 5, g ∈ CFSG.Sporadic.Fi22.lvl i := by
    intro i hi
    induction i with
    | zero => exact CFSG.Sporadic.Fi22.mem_lvl_zero g
    | succ i ih =>
      refine (CFSG.Sporadic.Fi22.chain_facts'.2.1 i
        (by rw [CFSG.Sporadic.Fi22.chainBase_size]; omega) g (ih (by omega))).1 (h _ ?_)
      have hi4 : i < 5 := by omega
      interval_cases i <;> decide
  have hc := CFSG.Sporadic.Fi22.chain_facts'.2.2 5 (by rw [CFSG.Sporadic.Fi22.chainBase_size])
  rw [CFSG.Sporadic.Fi22.chainBase_size, Finset.Ico_self, Finset.prod_empty] at hc
  have hb := Subgroup.eq_bot_of_card_eq _ hc
  have hg := hl 5 le_rfl
  rw [hb] at hg
  exact (Subgroup.mem_bot).1 hg

theorem model : Model letP E (wE (fP a b)) ∧
    ∀ u, chW letP u = true → wE (fP a b) u = 1 → E u [] = true :=
  eqB_model hA hAi hB hBi bs_lt sep_bs

noncomputable def rT (k : ℕ) : J := wE (fP a b) (nthW D.T k)

theorem rT_order {k : ℕ} (hk : k < 4) : orderOf (rT k) = 3 := by
  obtain ⟨hM, hc⟩ := model
  have h := okF_parts.2 k hk
  unfold chkT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨ot, h3⟩, hne⟩, -⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (hM.pow ot h3) (hM.ne_one hc ot hne)

theorem rT_fix {k : ℕ} (hk : k < 4) : fixN (n := 3510) (rT k) = nthN D.F k := by
  have h := okF_parts.2 k hk
  unfold chkT at h
  simp only [Bool.and_eq_true] at h
  rw [rT, ← fixB_eq hA hAi hB hBi (by norm_num : 3510 ≤ 64 * 55)]
  exact Nat.eq_of_beq_eq_true h.2

theorem F_inj : ∀ j j' : Fin 4, nthN D.F j = nthN D.F j' → j = j' := by decide

theorem ev_seed_a : wE (fP a b) [0] = a := by rw [wE_cons, wE_nil, one_mul, fP_zero]

theorem ev_seed_b : wE (fP a b) [2] = b := by rw [wE_cons, wE_nil, one_mul, fP_two]

theorem closure_seeds : Subgroup.closure ({wE (fP a b) [0], wE (fP a b) [2]} : Set J) = ⊤ := by
  rw [ev_seed_a, ev_seed_b]
  exact CFSG.Sporadic.Fi22.closure_ab

theorem top_of_stages {T : Subgroup J} (h : ∀ k, wE (fP a b) (nthW [[0], [2]] k) ∈ T) :
    T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  change wE (fP a b) [0] ∈ T at h0
  change wE (fP a b) [2] ∈ T at h1
  rw [ev_seed_a] at h0
  rw [ev_seed_b] at h1
  rw [eq_top_iff, ← CFSG.Sporadic.Fi22.closure_ab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem gen_path {i : ℕ} (hi : i < 2) :
    ∀ y, IsConj (rT i) y → SporKRestGenerating 3 y := by
  obtain ⟨hM, -⟩ := model
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi22.card_J]; norm_num)
  have h := (allLt_iff _ 2).1 Ck.okP i hi
  unfold chkP at h
  rw [Bool.and_eq_true] at h
  have ht := (okF_parts.2 i (by omega))
  unfold chkT at ht
  simp only [Bool.and_eq_true] at ht
  exact hM.generating_of_ctlA Nat.prime_three h.1 closure_seeds h.2 ht.1.1.1

theorem gen_cent {t y₂ g₂ : List ℕ} {M C : List (List ℕ)} {n nL : ℕ}
    (h : chkC E t y₂ g₂ M C n nL = true) (ht : chW letP t = true) :
    ∀ y, IsConj (wE (fP a b) t) y → SporKRestGenerating 3 y := by
  obtain ⟨hM, -⟩ := model
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi22.card_J]; norm_num)
  unfold chkC at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨hH, hL⟩, hs⟩, hS⟩ := h
  have hMc : chA letP M = true := (hM.clH_facts hH ht).2.1
  exact hM.generating_of_cl Nat.prime_three hH ht
    (top_of_stages (hM.mem_of_stages (hM.mem_of_cl_letters hH ht hL) hMc hs hS))

end CFSG.KD.SporCovBase.Fi22

end
