
module

public import Certificates.Kernel.FinModel5040.Chk5040
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataBase
public import CFSG.Certificates.Kernel.Misc.A7NatSound

public section

namespace CertificateChecks.KernelFM5040

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.Model.Facts
open CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KD.A7Nat CFSG.KC.A7Nat CFSG.KD.FM5040

variable {m : ℕ}

theorem movK_code (hm : m ≤ 32) (σ : Equiv.Perm (Fin m)) : movK m (code σ) = numMoved σ := by
  rw [movK, Nat.sub_eq, fix_code hm]
  have h : (Finset.univ.filter fun i : Fin m => σ i = i).card +
      (Finset.univ.filter fun i : Fin m => ¬ σ i = i).card = m := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have e : numMoved σ = (Finset.univ.filter fun i : Fin m => ¬ σ i = i).card := by
    unfold numMoved
    congr 1
  omega

theorem exK_code (hm : m ≤ 32) (L : List (Equiv.Perm (Fin m))) (σ : Equiv.Perm (Fin m)) :
    exK m (L.map code) (code σ) = exOf L σ := by
  rw [exK, exOf]
  by_cases h : σ ∈ L
  · have e : memL (code σ) (L.map code) = true := (memL_iff _ _).2 ((mem_map_code hm L σ).2 h)
    rw [e, if_pos h]
    exact movK_code hm σ
  · have e : memL (code σ) (L.map code) = false := by
      cases e : memL (code σ) (L.map code)
      · rfl
      · exact absurd ((mem_map_code hm L σ).1 ((memL_iff _ _).1 e)) h
    rw [e, if_neg h]

theorem invoK_code (hm : m ≤ 32) (σ : Equiv.Perm (Fin m)) :
    invoK m (code σ) = true ↔ σ * σ = 1 ∧ σ ≠ 1 := by
  rw [invoK, andB_iff, notB_iff, code_mul hm, code_one, beq_iff, beq_iff, code_eq_iff hm,
    code_eq_iff hm]

theorem cnt_code (hm : m ≤ 32) (L : List (Equiv.Perm (Fin m))) (y : Equiv.Perm (Fin m)) :
    cntL (comm m (code y)) (L.map code) = (L.filter fun p => decide (y * p = p * y)).length := by
  rw [cntL_eq, List.countP_map, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr fun p _ => ?_
  rw [Function.comp_apply, Bool.eq_iff_iff, comm_code hm, decide_eq_true_iff]

theorem orderOf_two {K G : Type*} [Group K] [Group G] (φ : K →* G) (hφ : Function.Injective φ)
    (x : K) (h1 : φ x * φ x = 1) (h2 : φ x ≠ 1) : orderOf x = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · apply hφ
    rw [map_pow, pow_two, h1, map_one]
  · rintro rfl
    exact h2 (map_one φ)

theorem facts_of (n : ℕ) [NeZero n] (hm : n + 4 ≤ 32) (a x g1 g2 : ℕ) (t : List ℕ)
    (ha : code (a0perm n) = a) (hx : code (emb n (x0 n)) = x)
    (h : allK (n + 4) (a :: x :: g1 :: g2 :: t) ((Rl n).map code) ((Sl n).map code)
      ((Cl n).map code) = true) :
    FactsProp n := by
  change andB (baseK _ a _) (andB (oddK _ a _) (andB (nodupL _)
    (andB (centK _ a x _) (etaK _ a x g1 g2 _ _)))) = true at h
  subst ha hx
  rw [andB_iff, andB_iff, andB_iff, andB_iff] at h
  obtain ⟨hb, ho, hn, hc, he⟩ := h
  simp only [baseK, oddK, centK, andB_iff, notB_iff, impB_iff, orB_iff, letB_eq, memL_iff,
    mem_map_code hm, code_mul hm, code_inv hm, code_one, conj_code hm, beq_iff, code_eq_iff hm,
    allL_map, anyL_map, movK_code hm, invoK_code hm, cnt_code hm] at hb ho hc
  simp only [etaK, andB_iff, memL_iff, mem_map_code hm, List.mem_map] at he
  obtain ⟨⟨ha0, ⟨p1, hp1, rfl⟩, ⟨p2, hp2, rfl⟩⟩, hu1, hu2, hu3, hpr⟩ := he
  simp only [letB_eq, andB_iff, code_mul hm, invoK_code hm, exK_code hm, beq_iff, allL_map, pairK,
    orB_iff, notB_iff, movK_code hm] at hu1 hu2 hu3 hpr
  obtain ⟨hsq, hnot, hnorm⟩ := hb
  refine ⟨hsq, hnot, hnorm, fun p hp h1 h2 => (ho p hp h1).1 h2, fun p hp h1 => (ho p hp h1).2,
    ((nodupL_iff _ hn).of_map _), fun y hy h1 h2 h3 => hc y hy ⟨h1, h2⟩ h3, ?_⟩
  intro K _ φ ψ hφ hCl hRl h0
  obtain ⟨c0, hc0⟩ := hCl _ ha0
  obtain ⟨c1, hc1⟩ := hCl _ hp1
  obtain ⟨c2, hc2⟩ := hCl _ hp2
  have hy0 : ψ c0 = emb n (x0 n) := h0 c0 hc0
  rcases hpr (ψ c1) (hRl c1) (ψ c2) (hRl c2) with h2 | h3 | h1
  · refine ⟨c2, orderOf_two φ hφ c2 (by rw [hc2]; exact hu2.1.1) (by rw [hc2]; exact hu2.1.2), ?_⟩
    rw [hc2, hu2.2]
    exact h2
  · refine ⟨c0 * c1, orderOf_two φ hφ _ (by simp only [map_mul, hc0, hc1]; exact hu3.1.1)
      (by simp only [map_mul, hc0, hc1]; exact hu3.1.2), ?_⟩
    simp only [map_mul, hc0, hc1, hu3.2, hy0]
    exact h3
  · refine ⟨c1 * c2 * (c1 * c2), orderOf_two φ hφ _
      (by simp only [map_mul, hc1, hc2]; exact hu1.1.1)
      (by simp only [map_mul, hc1, hc2]; exact hu1.1.2), ?_⟩
    simp only [map_mul, hc1, hc2, hu1.2]
    exact h1

theorem facts_of' (n : ℕ) [NeZero n] (hm : n + 4 ≤ 32) (M R S C : List ℕ)
    (hR : (((Tl n).map fun t => code (emb n t)) == R) = true)
    (hA : ([code (a0perm n), code (emb n (x0 n))] == M.take 2) = true)
    (hS : ((R ++ R.map fun c => mul (n + 4) c (M.headD 0)) == S) = true)
    (hC : ((S.filter fun c => comm (n + 4) (M.headD 0) c) == C) = true)
    (h : allK (n + 4) M R S C = true) : FactsProp n := by
  rcases M with _ | ⟨a, _ | ⟨x, _ | ⟨g1, _ | ⟨g2, t⟩⟩⟩⟩
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  have hA' : code (a0perm n) = a ∧ code (emb n (x0 n)) = x := by
    simpa using hA
  have hRe : (Rl n).map code = R := by
    rw [← beq_iff_eq.1 hR]
    simp only [Rl, List.map_map, Function.comp_def, flatPerm_eq]
  have hSe : (Sl n).map code = S := by
    rw [← beq_iff_eq.1 hS, ← hRe]
    simp only [Sl, List.map_append, List.map_map, Function.comp_def, flatPerm_eq, a0f_eq,
      List.headD_cons, ← hA'.1, code_mul hm]
  have hCe : (Cl n).map code = C := by
    rw [← beq_iff_eq.1 hC, ← hSe, Cl, List.filter_map]
    refine congrArg (List.map code) (List.filter_congr fun p _ => ?_)
    rw [Function.comp_apply, List.headD_cons, ← hA'.1, Bool.eq_iff_iff, decide_eq_true_iff,
      comm_code hm, a0f_eq]
  rw [← hRe, ← hSe, ← hCe] at h
  exact facts_of n hm a x g1 g2 t hA'.1 hA'.2 h

theorem bindR6 : (((Tl 6).map fun t => code (emb 6 t)) == R6) = true := by decide +kernel

theorem bindA6 : ([code (a0perm 6), code (emb 6 (x0 6))] == M6.take 2) = true := by decide +kernel

theorem bindS6 : ((R6 ++ R6.map fun c => mul (6 + 4) c (M6.headD 0)) == S6) = true := by
  decide +kernel

theorem bindC6 : ((S6.filter fun c => comm (6 + 4) (M6.headD 0) c) == C6) = true := by
  decide +kernel

theorem bindR7 : (((Tl 7).map fun t => code (emb 7 t)) == R7) = true := by decide +kernel

theorem bindA7 : ([code (a0perm 7), code (emb 7 (x0 7))] == M7.take 2) = true := by decide +kernel

theorem bindS7 : ((R7 ++ R7.map fun c => mul (7 + 4) c (M7.headD 0)) == S7) = true := by
  decide +kernel

theorem bindC7 : ((S7.filter fun c => comm (7 + 4) (M7.headD 0) c) == C7) = true := by
  decide +kernel

theorem facts6 : FactsProp 6 :=
  facts_of' 6 (by norm_num) M6 R6 S6 C6 bindR6 bindA6 bindS6 bindC6 ch5040_6

theorem facts7 : FactsProp 7 :=
  facts_of' 7 (by norm_num) M7 R7 S7 C7 bindR7 bindA7 bindS7 bindC7 ch5040_7

end CertificateChecks.KernelFM5040

end
