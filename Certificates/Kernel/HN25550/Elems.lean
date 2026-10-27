module

public import Certificates.Kernel.HN25550.Mat
public import CFSG.Sporadic.HNOddCore.SixA
public import CFSG.Sporadic.HNSchreier.ThreeSpec

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHN25550

open CFSG.KS.WordRegs CFSG.KD.HN25550 CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
open CFSG.ONSchreier.Native

noncomputable abbrev hjc : List ℕ := HJ.map fun g => 2 * g + 1

theorem ties :
    triOK RW r0 Data.subgroupProgram SP = true ∧
    tieW RW (triRegs r0 Data.subgroupProgram SP 1) (hjc.getD 0 0) = true ∧
    tieW RW (triRegs r0 Data.subgroupProgram SP 2) (hjc.getD 1 0) = true ∧
    (HJ.length == 17) = true ∧
    ((List.range 15).all fun u =>
      tieW RW ((LocalData.strongWords[u + 2]!).map (sgnC hjc)) (hjc.getD (u + 2) 0)) = true ∧
    (C6J == [1, 2, 5]) = true ∧ (C6.length == 3) = true ∧
    ((List.range 3).all fun k =>
      lettersJ 17 InvData.c6Words[C6J.getD k 0]! &&
      tieW RW ((InvData.c6Words[C6J.getD k 0]!).map (sgnC hjc)) (2 * C6.getD k 0 + 1)) = true ∧
    tieW RW (InvData.m2ConjRoot.map fun l => if l = 1 then 1 else 3) (2 * U + 1) = true ∧
    lettersJ 17 InvData.m2ConjH = true ∧
    tieW RW (InvData.m2ConjH.map (sgnC hjc)) (2 * HC + 1) = true ∧
    tieW RW [2 * U + 1, 2 * HC + 1] (2 * G6C + 1) = true ∧
    bprOK RW r0 InvData.m2Prog M2 = true ∧
    tieW RW (bprRegs r0 InvData.m2Prog M2 1) M2R1 = true ∧
    tieW RW [2 * G6C, M2R1, 2 * G6C + 1] (2 * E61 + 1) = true ∧
    (G6S == [1, 2, 5, 10]) = true ∧ (G6 == [C6.getD 0 0, C6.getD 1 0, C6.getD 2 0, E61]) = true ∧
    (PW.length == 4) = true ∧ (PR.length == 4) = true ∧
    ((List.range 4).all fun j =>
      tieW RW ((PW.getD j []).map (g6code G6S G6)) (2 * PR.getD j 0 + 1) &&
        decide (PR.getD j 0 < 46)) = true := by
  have h := ties_ok
  unfold tiesK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, -, -, h⟩ := h
  exact h

theorem runProg_tri : ∀ (P : List (ℕ × ℕ × ℕ)) (R : ℕ → List ℕ) (Gs : List ℕ) (regs : ℕ → JH),
    triOK RW R P Gs = true → (∀ r, regs r = wordEl rEl (R r)) →
    ∀ r, runProg regs P r = wordEl rEl (triRegs R P Gs r)
  | [], R, Gs, regs, _, hR, r => by
    cases Gs <;> exact hR r
  | (a, b, c) :: P, R, [], regs, h, _, _ => by simp [triOK] at h
  | (a, b, c) :: P, R, g :: Gs, regs, h, hR, r => by
    simp only [triOK, Bool.and_eq_true] at h
    have ht := tieW_sound rEl_roots h.1
    change runProg (Function.update regs c (regs a * regs b)) P r =
      wordEl rEl (triRegs (updW R c [2 * g + 1]) P Gs r)
    refine runProg_tri P _ Gs _ h.2 (fun s => ?_) r
    unfold updW
    by_cases hs : s = c
    · subst hs
      rw [Function.update_self, if_pos rfl, hR, hR, ← wordEl_append, ht, wordEl_single]
    · rw [Function.update_of_ne hs, if_neg hs, hR]

theorem progRunG_bpr : ∀ (P : List (Bool × ℕ × ℕ × ℕ)) (R : ℕ → List ℕ) (Gs : List ℕ)
    (regs : ℕ → JH), bprOK RW R P Gs = true → (∀ r, regs r = wordEl rEl (R r)) →
    ∀ r, progRunG regs P r = wordEl rEl (bprRegs R P Gs r)
  | [], R, Gs, regs, _, hR, r => by
    cases Gs <;> exact hR r
  | (true, a, b, c) :: P, R, [], regs, h, _, _ => by simp [bprOK] at h
  | (true, a, b, c) :: P, R, g :: Gs, regs, h, hR, r => by
    simp only [bprOK, Bool.and_eq_true] at h
    have ht := tieW_sound rEl_roots h.1
    change progRunG (Function.update regs c (regs a * regs b)) P r =
      wordEl rEl (bprRegs (updW R c [2 * g + 1]) P Gs r)
    refine progRunG_bpr P _ Gs _ h.2 (fun s => ?_) r
    unfold updW
    by_cases hs : s = c
    · subst hs
      rw [Function.update_self, if_pos rfl, hR, hR, ← wordEl_append, ht, wordEl_single]
    · rw [Function.update_of_ne hs, if_neg hs, hR]
  | (false, a, b, d) :: P, R, Gs, regs, h, hR, r => by
    simp only [bprOK] at h
    change progRunG (Function.update regs b (regs a)⁻¹) P r =
      wordEl rEl (bprRegs (updW R b (invW (R a))) P Gs r)
    refine progRunG_bpr P _ Gs _ h (fun s => ?_) r
    unfold updW
    by_cases hs : s = b
    · subst hs
      rw [Function.update_self, if_pos rfl, hR, wordEl_invW]
    · rw [Function.update_of_ne hs, if_neg hs, hR]

theorem rEl_zero : rEl 0 = aJ := by
  rw [rEl_eq, if_pos rfl]

theorem rEl_one : rEl 1 = bJ := by
  rw [rEl_eq, if_neg (by norm_num), if_pos rfl]

theorem codeEl_one : codeEl rEl 1 = aJ := by
  have h := codeEl_odd (ρ := rEl) 0
  rw [rEl_zero] at h
  exact h

theorem codeEl_three : codeEl rEl 3 = bJ := by
  have h := codeEl_odd (ρ := rEl) 1
  rw [rEl_one] at h
  exact h

theorem jRegs0_eq (r : ℕ) : jRegs0 r = wordEl rEl (r0 r) := by
  unfold jRegs0 r0
  by_cases h1 : r = 1
  · rw [if_pos h1, if_pos h1, wordEl_single, codeEl_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : r = 2
    · rw [if_pos h2, if_pos h2, wordEl_single, codeEl_three]
    · rw [if_neg h2, if_neg h2]
      rfl

theorem hj_len : HJ.length = 17 := beq_iff_eq.1 ties.2.2.2.1

theorem h1_eq : h1J = codeEl rEl (hjc.getD 0 0) := by
  rw [h1J, jRegs, runProg_tri _ _ _ _ ties.1 jRegs0_eq 1, tieW_sound rEl_roots ties.2.1]

theorem h2_eq : h2J = codeEl rEl (hjc.getD 1 0) := by
  rw [h2J, jRegs, runProg_tri _ _ _ _ ties.1 jRegs0_eq 2, tieW_sound rEl_roots ties.2.2.1]

theorem strongWords_letters {j : ℕ} (hj : j < 17) (h2 : 2 ≤ j) :
    plettersOK j LocalData.strongWords[j]! = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hw, -⟩ := local_parts_data
  unfold plettersOK
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, hle⟩ := hw j hj h2 l hl
  simp [h0, hle]

theorem hJ_eq : ∀ j < 17, hJ j = codeEl rEl (hjc.getD j 0) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · interval_cases j
      · rw [hJ, gStrong_of_lt _ _ (by simp)]
        exact h1_eq
      · rw [hJ, gStrong_of_lt _ _ (by simp)]
        exact h2_eq
    · rw [hJ, gStrong_of_ge _ _ (by simpa using h2),
        evalWord_ptoLetters_eq (gStrong [h1J, h2J] LocalData.strongWords) _
          (strongWords_letters hj h2)]
      have hu := List.all_eq_true.1 ties.2.2.2.2.1 (j - 2) (List.mem_range.2 (by omega))
      have e : j - 2 + 2 = j := by omega
      rw [e] at hu
      rw [← tieW_sound rEl_roots hu, wordEl_sgnC (f := gStrong [h1J, h2J] LocalData.strongWords)]
      intro l hl
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hw, -⟩ := local_parts_data
      obtain ⟨h0, hle⟩ := hw j hj h2 l hl
      exact (ih _ (by omega) (by omega)).symm

theorem hWordJ_eq {w : List ℤ} (hw : lettersJ 17 w = true) :
    hWordJ w = wordEl rEl (w.map (sgnC hjc)) := by
  rw [hWordJ, wordEl_sgnC (f := hJ)]
  intro l hl
  unfold lettersJ at hw
  have := List.all_eq_true.1 hw l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact (hJ_eq _ (by omega)).symm

theorem c6_parts : C6J = [1, 2, 5] ∧ C6.length = 3 ∧ ∀ k < 3,
    lettersJ 17 InvData.c6Words[C6J.getD k 0]! = true ∧
    tieW RW ((InvData.c6Words[C6J.getD k 0]!).map (sgnC hjc)) (2 * C6.getD k 0 + 1) = true := by
  obtain ⟨-, -, -, -, -, h1, h2, h3, -⟩ := ties
  refine ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2, fun k hk => ?_⟩
  have := List.all_eq_true.1 h3 k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at this
  exact this

theorem c6G_eq {k : ℕ} (hk : k < 3) : c6G (C6J.getD k 0) = rEl (C6.getD k 0) := by
  obtain ⟨-, -, h⟩ := c6_parts
  obtain ⟨hl, ht⟩ := h k hk
  rw [c6G, hWordJ_eq hl, tieW_sound rEl_roots ht, codeEl_odd]

theorem seedWordJ_eq (w : List ℕ) :
    seedWordJ w = wordEl rEl (w.map fun l => if l = 1 then 1 else 3) := by
  rw [seedWordJ, wordEl, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply]
  by_cases h : l = 1
  · rw [if_pos h, if_pos h, codeEl_one]
  · rw [if_neg h, if_neg h, codeEl_three]

theorem g6cJ_eq : g6cJ = rEl G6C := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4, -⟩ := ties
  rw [g6cJ, seedWordJ_eq, tieW_sound rEl_roots h1, hWordJ_eq h2, tieW_sound rEl_roots h3,
    ← codeEl_odd (ρ := rEl) G6C, ← tieW_sound rEl_roots h4, wordEl_cons, wordEl_single]

theorem m2RegsJ_one : m2RegsJ 1 = codeEl rEl M2R1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := ties
  rw [m2RegsJ, progRunG_bpr _ _ _ _ h1 jRegs0_eq 1, tieW_sound rEl_roots h2]

theorem e6J_one : e6J 1 = rEl E61 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := ties
  rw [e6J, g6cJ_eq, m2RegsJ_one, ← codeEl_odd (ρ := rEl) E61, ← tieW_sound rEl_roots h1,
    wordEl_cons, wordEl_cons, wordEl_single, codeEl_even, codeEl_odd]

theorem g6_parts : G6S = [1, 2, 5, 10] ∧ G6 = [C6.getD 0 0, C6.getD 1 0, C6.getD 2 0, E61] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := ties
  exact ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2⟩

theorem g6_eq {s : ℕ} (hs : s ∈ G6S) : g6 s = codeEl rEl (g6code G6S G6 s) := by
  obtain ⟨h1, h2⟩ := g6_parts
  obtain ⟨hC, -, -⟩ := c6_parts
  unfold g6code
  rw [codeEl_odd, h2]
  rw [h1] at hs ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · have := c6G_eq (k := 0) (by norm_num)
    rw [hC] at this
    rw [g6, if_pos (by norm_num)]
    exact this
  · have := c6G_eq (k := 1) (by norm_num)
    rw [hC] at this
    rw [g6, if_pos (by norm_num)]
    exact this
  · have := c6G_eq (k := 2) (by norm_num)
    rw [hC] at this
    rw [g6, if_pos (by norm_num)]
    exact this
  · rw [g6, if_neg (by norm_num)]
    exact e6J_one

theorem pr_parts : PW.length = 4 ∧ PR.length = 4 ∧ ∀ j < 4,
    tieW RW ((PW.getD j []).map (g6code G6S G6)) (2 * PR.getD j 0 + 1) = true ∧
      PR.getD j 0 < 46 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3⟩ := ties
  refine ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2, fun j hj => ?_⟩
  have := List.all_eq_true.1 h3 j (List.mem_range.2 hj)
  rw [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

@[expose] noncomputable def g6F
    (s : ℕ) : C6 :=
  if h : s < 12 then g6C ⟨s, h⟩ else 1

@[expose] noncomputable def pgen
    (j : ℕ) : C6 :=
  ((PW.getD j []).map g6F).prod


theorem pw_letters {j : ℕ} : ∀ s ∈ PW.getD j [], s ∈ G6S := by
  have h := pw_ok.2.1
  intro s hs
  by_cases hj : j < PW.length
  · rw [List.getD_eq_getElem _ _ hj] at hs
    have := List.all_eq_true.1 h _ (List.getElem_mem hj)
    exact of_decide_eq_true (List.all_eq_true.1 this s hs)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : PW.length ≤ j)] at hs

theorem g6F_coe {s : ℕ} (hs : s ∈ G6S) : ((g6F s : C6) : JH) = g6 s := by
  have h1 := g6_parts.1
  rw [h1] at hs
  have hs12 : s < 12 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  rw [g6F, dif_pos hs12]
  rfl

theorem pgen_eq {j : ℕ} (hj : j < 4) : ((pgen j : C6) : JH) = rEl (PR.getD j 0) := by
  obtain ⟨-, -, h⟩ := pr_parts
  obtain ⟨ht, -⟩ := h j hj
  rw [← codeEl_odd (ρ := rEl), ← tieW_sound rEl_roots ht, pgen]
  change C6.subtype (((PW.getD j []).map g6F).prod) = _
  rw [map_list_prod, List.map_map, wordEl, List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  simp only [Function.comp_apply, Subgroup.coe_subtype]
  rw [g6F_coe (pw_letters s hs), g6_eq (pw_letters s hs)]

end CertificateChecks.KernelHN25550

end
