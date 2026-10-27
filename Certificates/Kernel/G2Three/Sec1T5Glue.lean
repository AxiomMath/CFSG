module

public import Certificates.Kernel.G2Three.Sec1T5Checks
public import CFSG.Certificates.Kernel.G2Three.Sec1Mat9
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T5Facts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameLe
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LGroupA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.SylowConj
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.CountE
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabHom
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred4

public section

namespace CFSG.KD.G2Three.Sec1.T5Glue

open Subgroup CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KC.G2Three CFSG.KC.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] noncomputable def LD (l : ℕ) : ℕ := pkPc (letterP l)

@[expose] noncomputable def wD : List ℕ → ℕ
  | [] => ONEP
  | l :: w => MULP (LD l) (wD w)

@[expose] def IsW (w : List ℕ) : Prop := ∀ l ∈ w, l < 4

theorem letter_ok (l : ℕ) (hl : l < 4) :
    canonPc (letterP l) = true ∧ pcFlag (letterP l) = false := by
  interval_cases l
  · exact ⟨by decide +kernel, by simp [letterP, gx0P, pcFlag_mkPc]⟩
  · exact ⟨by decide +kernel, by simp [letterP, gx1P, pcFlag_mkPc]⟩
  · exact ⟨by decide +kernel, by simp [letterP, gy0P, pcFlag_mkPc]⟩
  · exact ⟨by decide +kernel, by simp [letterP, gy1P, pcFlag_mkPc]⟩

variable {G : Type} [Group G] [Finite G] (m : G23Model G)

theorem enc_letter {l : ℕ} (hl : l < 4) : Enc m.ρ (LD l) (letterG m l) := by
  obtain ⟨hc, hf⟩ := letter_ok l hl
  exact ⟨okP_pkPc hc, by rw [rho_letterG, LD, decP_pkPc hc hf]⟩

theorem enc_word : ∀ {w : List ℕ}, IsW w → Enc m.ρ (wD w) (wordG m w)
  | [], _ => by
    have e : wordG m [] = 1 := by simp [wordG]
    rw [e, wD]
    exact enc_one m.ρ
  | l :: w, hw => by
    have e : wordG m (l :: w) = letterG m l * wordG m w := by simp [wordG]
    rw [e, wD]
    exact enc_mul m.ρ (enc_letter m (hw l (by simp)))
      (enc_word (fun l' hl' => hw l' (by simp [hl'])))

theorem wordG_append (v w : List ℕ) : wordG m (v ++ w) = wordG m v * wordG m w := by
  simp [wordG, List.map_append, List.prod_append]

theorem word_eq {v w : List ℕ} (hv : IsW v) (hw : IsW w) (h : wD v = wD w) :
    wordG m v = wordG m w :=
  enc_unique m.inj (enc_word m hv) (h ▸ enc_word m hw)

@[expose] def W0 : List ℕ := [0, 2, 2, 0]
@[expose] def W0i : List ℕ := [0, 0, 2, 0, 0]
@[expose] def W1 : List ℕ := [1, 3, 3, 1]
@[expose] def W1i : List ℕ := [1, 1, 3, 1, 1]

@[expose] def u1W : List ℕ := W0 ++ [1] ++ W0i
@[expose] def u1iW : List ℕ := W0 ++ [1, 1] ++ W0i
@[expose] def b1W : List ℕ := W0 ++ W1 ++ W0i
@[expose] def u2W : List ℕ := W1 ++ [0] ++ W1i
@[expose] def u2iW : List ℕ := W1 ++ [0, 0] ++ W1i
@[expose] def b2W : List ℕ := W1 ++ W0 ++ W1i
@[expose] def h0W : List ℕ := W1 ++ W1
@[expose] def a1W : List ℕ := u1W ++ b1W ++ b1W ++ b1W ++ u1iW
@[expose] def a2W : List ℕ := u2W ++ b2W ++ b2W ++ b2W ++ u2iW

@[expose] def g5W (s : ℕ) : List ℕ := [a1W, b1W, a2W, b2W, h0W, k3W, tW].getD s []

theorem isW_g5W {s : ℕ} (hs : s < 7) : IsW (g5W s) := by
  interval_cases s <;> (unfold IsW; decide)

theorem isW_W0 : IsW (W0 ++ W0i) ∧ IsW (W1 ++ W1i) ∧ IsW (u1W ++ u1iW) ∧ IsW (u2W ++ u2iW) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold IsW; decide)

theorem wD_inv : wD (W0 ++ W0i) = wD [] ∧ wD (W1 ++ W1i) = wD [] ∧ wD (u1W ++ u1iW) = wD [] ∧
    wD (u2W ++ u2iW) = wD [] :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

private theorem inv_of_word {v w : List ℕ} (hvw : IsW (v ++ w)) (h : wD (v ++ w) = wD []) :
    (wordG m v)⁻¹ = wordG m w := by
  have e := word_eq m hvw (fun l hl => by simp at hl) h
  rw [wordG_append] at e
  have e' : wordG m [] = 1 := by simp [wordG]
  rw [e'] at e
  exact (eq_inv_of_mul_eq_one_right e).symm

theorem mn0_eq : mn0 m = wordG m W0 := by
  simp [mn0, wordG, W0, letterG, pow_two, mul_assoc]

theorem mn1_eq : mn1 m = wordG m W1 := by
  simp [mn1, wordG, W1, letterG, pow_two, mul_assoc]

theorem gX1_eq : m.gX1 = wordG m [1] := by simp [wordG, letterG]

theorem gX0_eq : m.gX0 = wordG m [0] := by simp [wordG, letterG]

theorem u1_eq : (frameOf m).u₁ = wordG m u1W := by
  have e : (frameOf m).u₁ = mn0 m * m.gX1 * (mn0 m)⁻¹ := rfl
  rw [e, mn0_eq, gX1_eq, inv_of_word m isW_W0.1 wD_inv.1, u1W, wordG_append, wordG_append]

theorem u2_eq : (frameOf m).u₂ = wordG m u2W := by
  have e : (frameOf m).u₂ = mn1 m * m.gX0 * (mn1 m)⁻¹ := rfl
  rw [e, mn1_eq, gX0_eq, inv_of_word m isW_W0.2.1 wD_inv.2.1, u2W, wordG_append, wordG_append]

theorem b1_eq : (frameOf m).b₁ = wordG m b1W := by
  have e : (frameOf m).b₁ = mn0 m * mn1 m * (mn0 m)⁻¹ := rfl
  rw [e, mn0_eq, mn1_eq, inv_of_word m isW_W0.1 wD_inv.1, b1W, wordG_append, wordG_append]

theorem b2_eq : (frameOf m).b₂ = wordG m b2W := by
  have e : (frameOf m).b₂ = mn1 m * mn0 m * (mn1 m)⁻¹ := rfl
  rw [e, mn0_eq, mn1_eq, inv_of_word m isW_W0.2.1 wD_inv.2.1, b2W, wordG_append, wordG_append]

theorem h0_eq : (frameOf m).h₀ = wordG m h0W := by
  have e : (frameOf m).h₀ = mn1 m ^ 2 := rfl
  rw [e, mn1_eq, h0W, wordG_append, pow_two]

theorem a1_eq : (frameOf m).a₁ = wordG m a1W := by
  have e : (frameOf m).a₁ = (frameOf m).u₁ * (frameOf m).b₁ ^ 3 * (frameOf m).u₁⁻¹ := rfl
  have hi : (frameOf m).u₁⁻¹ = wordG m u1iW := by
    rw [u1_eq]
    exact inv_of_word m isW_W0.2.2.1 wD_inv.2.2.1
  rw [e, hi, u1_eq, b1_eq, a1W]
  simp only [wordG_append, pow_succ, pow_zero, one_mul, mul_assoc]

theorem a2_eq : (frameOf m).a₂ = wordG m a2W := by
  have e : (frameOf m).a₂ = (frameOf m).u₂ * (frameOf m).b₂ ^ 3 * (frameOf m).u₂⁻¹ := rfl
  have hi : (frameOf m).u₂⁻¹ = wordG m u2iW := by
    rw [u2_eq]
    exact inv_of_word m isW_W0.2.2.2 wD_inv.2.2.2
  rw [e, hi, u2_eq, b2_eq, a2W]
  simp only [wordG_append, pow_succ, pow_zero, one_mul, mul_assoc]

theorem gen5_eq {s : ℕ} (hs : s < 7) : gen5 m s = wordG m (g5W s) := by
  interval_cases s
  · simp only [gen5, if_pos (show 0 < 5 by norm_num), sGen_zero]
    exact a1_eq m
  · simp only [gen5, if_pos (show 1 < 5 by norm_num), sGen_one]
    exact b1_eq m
  · simp only [gen5, if_pos (show 2 < 5 by norm_num), sGen_two]
    exact a2_eq m
  · simp only [gen5, if_pos (show 3 < 5 by norm_num), sGen_three]
    exact b2_eq m
  · simp only [gen5, if_pos (show 4 < 5 by norm_num), sGen_four]
    exact h0_eq m
  · simp [gen5, g5W]
  · simp [gen5, g5W]

theorem q5U_gen : ∀ s < 7, Q5U s = wD (g5W s) := by
  intro s hs
  interval_cases s
  all_goals exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem enc_gen5 {s : ℕ} (hs : s < 7) : Enc m.ρ (Q5U s) (gen5 m s) := by
  rw [gen5_eq m hs, q5U_gen s hs]
  exact enc_word m (isW_g5W hs)

@[expose] def defs5 : List (ℕ × ℕ) :=
  [(0, 2), (1, 3), (1, 1), (0, 1), (11, 2), (8, 4), (6, 5), (2, 6), (0, 3), (16, 4), (0, 0),
    (18, 6), (19, 6), (20, 20), (5, 5), (9, 10), (0, 6), (4, 5), (5, 6), (1, 26), (4, 26),
    (0, 28), (0, 14), (1, 14), (6, 14), (6, 26)]

@[expose] def stepU (acc : List G) (d : ℕ × ℕ) : List G := acc ++ [acc.getD d.1 1 * acc.getD d.2 1]

@[expose] def uE (i : ℕ) : G :=
  (defs5.foldl stepU (((List.range 7).map (gen5 m)) ++ [1])).getD i 1

theorem q5U_defs : ∀ j < 26, (defs5.getD j (0, 0)).1 < j + 8 ∧ (defs5.getD j (0, 0)).2 < j + 8 ∧
    Q5U (j + 8) = MULP (Q5U (defs5.getD j (0, 0)).1) (Q5U (defs5.getD j (0, 0)).2) := by
  intro j hj
  interval_cases j
  all_goals exact ⟨by decide, by decide, Nat.eq_of_beq_eq_true (by quickRfl)⟩

private theorem enc_fold : ∀ (ds : List (ℕ × ℕ)) (k : ℕ) (acc : List G), acc.length = k →
    (∀ i < k, Enc m.ρ (Q5U i) (acc.getD i 1)) →
    (∀ j < ds.length, (ds.getD j (0, 0)).1 < k + j ∧ (ds.getD j (0, 0)).2 < k + j ∧
      Q5U (k + j) = MULP (Q5U (ds.getD j (0, 0)).1) (Q5U (ds.getD j (0, 0)).2)) →
    ∀ i < k + ds.length, Enc m.ρ (Q5U i) ((ds.foldl stepU acc).getD i 1)
  | [], k, acc, _, hacc, _ => by simpa using hacc
  | d :: ds, k, acc, hk, hacc, hds => by
    have h0 := hds 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    have hacc' : ∀ i < k + 1, Enc m.ρ (Q5U i) ((stepU acc d).getD i 1) := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [stepU, List.getD_append _ _ _ _ (by omega)]
        exact hacc i hi
      · rw [stepU, List.getD_append_right _ _ _ _ (by omega), hk, Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [h0.2.2]
        exact enc_mul m.ρ (hacc _ h0.1) (hacc _ h0.2.1)
    intro i hi
    have := enc_fold ds (k + 1) (stepU acc d) (by simp [stepU, hk]) hacc' (fun j hj => by
      have h := hds (j + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at h
      rw [show k + 1 + j = k + (j + 1) by omega]
      exact ⟨by omega, by omega, h.2.2⟩) i (by simp at hi; omega)
    simpa only [List.foldl_cons] using this

theorem enc_uE {i : ℕ} (hi : i < 34) : Enc m.ρ (Q5U i) (uE m i) := by
  have hl : defs5.length = 26 := rfl
  refine enc_fold m defs5 8 _ (by simp) (fun i hi => ?_) (fun j hj => ?_) i (by rw [hl]; omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, List.getElem_range]
      exact enc_gen5 m hi
    · rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
      have h7 : Q5U 7 = ONEP := by
        have h := q5_one
        simp only [Bool.and_eq_true, Nat.beq_eq] at h
        exact h.1.1.1.1.1.1.1.1.1.1
      rw [h7]
      exact enc_one m.ρ
  · rw [Nat.add_comm 8 j]
    exact q5U_defs j (by rw [hl] at hj; exact hj)

private theorem getD_mem {K : Subgroup G} {acc : List G} (h : ∀ x ∈ acc, x ∈ K) (i : ℕ) :
    acc.getD i 1 ∈ K := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : acc[i]? with
  | none => exact K.one_mem
  | some x => exact h x (List.mem_of_getElem? hx)

private theorem mem_fold (K : Subgroup G) :
    ∀ (ds : List (ℕ × ℕ)) (acc : List G), (∀ x ∈ acc, x ∈ K) → ∀ x ∈ ds.foldl stepU acc, x ∈ K
  | [], _, h => h
  | d :: ds, acc, h => mem_fold K ds _ (by
      intro x hx
      simp only [stepU, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · exact K.mul_mem (getD_mem h d.1) (getD_mem h d.2))

theorem uE_mem (i : ℕ) : uE m i ∈ g23T5 m := by
  refine getD_mem (mem_fold _ defs5 _ ?_) i
  intro x hx
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hx
  rcases hx with ⟨s, hs, rfl⟩ | rfl
  · exact subset_closure ⟨s, hs, rfl⟩
  · exact (g23T5 m).one_mem

attribute [local irreducible] uE

theorem q5_ones : Q5U 7 = ONEP ∧ Q5X 0 = ONEP ∧ Q5S 0 = ONEP ∧ Q5A 0 = ONEP ∧ Q5B 0 = ONEP ∧
    Q5P 0 = ONEP ∧ Q5C 0 = ONEP ∧ Q5J 0 = ONEP ∧ Q59 0 = 273 ∧ Q5RJ 0 = 0 ∧ Q5RAR 0 = 0 := by
  have h := q5_one
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem uE_gen {s : ℕ} (hs : s < 7) : uE m s = gen5 m s :=
  enc_unique m.inj (enc_uE m (by omega)) (enc_gen5 m hs)

theorem uE_seven : uE m 7 = 1 :=
  enc_unique m.inj (enc_uE m (by norm_num)) (by rw [q5_ones.1]; exact enc_one m.ρ)

theorem uE_mul_eq {a b c d : ℕ} (ha : a < 34) (hb : b < 34) (hc : c < 34) (hd : d < 34)
    (h : MULP (Q5U a) (Q5U b) = MULP (Q5U c) (Q5U d)) : uE m a * uE m b = uE m c * uE m d :=
  mul_eq_of_MULP m.inj (enc_uE m ha) (enc_uE m hb) (enc_uE m hc) (enc_uE m hd) h

theorem rel5 {q a b c d : ℕ} (hq : q < 48) (ha : Q5RA q = a) (hb : Q5RB q = b) (hc : Q5RC q = c)
    (hd : Q5RD q = d) (h34 : a < 34 ∧ b < 34 ∧ c < 34 ∧ d < 34) :
    uE m a * uE m b = uE m c * uE m d := by
  have h : MULP (Q5U (Q5RA q)) (Q5U (Q5RB q)) = MULP (Q5U (Q5RC q)) (Q5U (Q5RD q)) :=
    eqK_at q5_rel (by norm_num) q hq
  rw [ha, hb, hc, hd] at h
  exact uE_mul_eq m h34.1 h34.2.1 h34.2.2.1 h34.2.2.2 h

theorem rl (q a b c d : ℕ) (h : (Nat.beq (Q5RA q) a && Nat.beq (Q5RB q) b && Nat.beq (Q5RC q) c &&
    Nat.beq (Q5RD q) d && Nat.blt q 48 && Nat.blt a 34 && Nat.blt b 34 && Nat.blt c 34 &&
    Nat.blt d 34) = true) : uE m a * uE m b = uE m c * uE m d := by
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hq⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  exact rel5 m hq ha hb hc hd ⟨h1, h2, h3, h4⟩

theorem uE_gen' (s : ℕ) (hs : s < 7) : uE m s = gen5 m s := uE_gen m hs

theorem uE_a1a2 : uE m 8 = (frameOf m).a₁ * (frameOf m).a₂ := by
  have h := rl m 0 0 2 8 7 (by quickRfl)
  rw [uE_seven, mul_one, uE_gen' m 0 (by norm_num), uE_gen' m 2 (by norm_num)] at h
  rw [← h]
  simp [gen5, sGen_zero, sGen_two]

theorem uE_b1b2 : uE m 9 = (frameOf m).b₁ * (frameOf m).b₂ := by
  have h := rl m 1 1 3 9 7 (by quickRfl)
  rw [uE_seven, mul_one, uE_gen' m 1 (by norm_num), uE_gen' m 3 (by norm_num)] at h
  rw [← h]
  simp [gen5, sGen_one, sGen_three]

theorem uE_z : uE m 10 = (frameOf m).z := by
  have h := rl m 2 1 1 10 7 (by quickRfl)
  rw [uE_seven, mul_one, uE_gen' m 1 (by norm_num)] at h
  rw [← h]
  simp [gen5, sGen_one, SFrame.z, pow_two]

theorem F_gens : (∀ s < 3, uE m (s + 8) * uE m (s + 8) = 1) ∧
    ∀ s < 3, ∀ t < 3, uE m (s + 8) * uE m (t + 8) = uE m (t + 8) * uE m (s + 8) := by
  have i8 := rl m 28 8 8 7 7 (by quickRfl)
  have i9 := rl m 29 9 9 7 7 (by quickRfl)
  have i10 := rl m 30 10 10 7 7 (by quickRfl)
  have c89 := rl m 31 8 9 9 8 (by quickRfl)
  have c810 := rl m 32 8 10 10 8 (by quickRfl)
  have c910 := rl m 33 9 10 10 9 (by quickRfl)
  rw [uE_seven, mul_one] at i8 i9 i10
  refine ⟨fun s hs => ?_, fun s hs t ht => ?_⟩
  · interval_cases s
    exacts [i8, i9, i10]
  · interval_cases s <;> interval_cases t
    exacts [rfl, c89, c810, c89.symm, rfl, c910, c810.symm, c910.symm, rfl]

theorem tabX : TabOf m.ρ Q5X 1344 (closure ((fun s => uE m (11 + 3 * s)) '' {s | s < 2}) : Set G) := by
  have key : ∀ i lo, closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 lo 448 7 =
      true → lo ≤ i → i < lo + 448 →
        Q5XPOS i < 1344 ∧ Q5X (Q5XPOS i) = MULP (Q5X (i / 2)) (Q5U (11 + 3 * (i % 2))) := by
    intro i lo h h1 h2
    have := closP_at h (by norm_num) (i - lo) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact this
  have hcl : ∀ i < 1344 * 2,
      Q5XPOS i < 1344 ∧ Q5X (Q5XPOS i) = MULP (Q5X (i / 2)) (Q5U (11 + 3 * (i % 2))) := by
    intro i hi
    by_cases h0 : i < 448
    · exact key i 0 q5_closX0 (by omega) (by omega)
    by_cases h1 : i < 896
    · exact key i 448 q5_closX1 (by omega) (by omega)
    by_cases h2 : i < 1344
    · exact key i 896 q5_closX2 (by omega) (by omega)
    by_cases h3 : i < 1792
    · exact key i 1344 q5_closX3 (by omega) (by omega)
    by_cases h4 : i < 2240
    · exact key i 1792 q5_closX4 (by omega) (by omega)
    · exact key i 2240 q5_closX5 (by omega) (by omega)
  exact tab_closure m.inj (Gd := fun s => Q5U (11 + 3 * s)) (by norm_num)
    (fun s hs => enc_uE m (by omega)) q5_ones.2.1 hcl (parK_at q5_parX (by norm_num))

theorem T5_eq : closure ((fun s => uE m (11 + 3 * s)) '' {s | s < 2}) = g23T5 m := by
  apply le_antisymm
  · rw [closure_le]
    rintro x ⟨s, -, rfl⟩
    exact uE_mem m _
  · rw [g23T5, closure_le]
    rintro x ⟨s, hs, rfl⟩
    have h := idxK_at q5_genX (by norm_num) s hs
    have he : Enc m.ρ (Q5X (Q5I5 s)) (gen5 m s) := by
      rw [h.2]
      exact enc_gen5 m hs
    exact mem_of_tabOf m.inj (tabX m) h.1 he

theorem card_T5 : Nat.card (g23T5 m) = 1344 := by
  rw [← T5_eq]
  exact tab_card m.inj (tabX m) (sort_inj q5_sortX (by norm_num))

theorem q5FG_eq : ∀ s < 3, Q5FG s = s + 8 := by
  intro s hs
  interval_cases s
  all_goals exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem tabF : TabOf m.ρ Q5F 8 (closure ((fun s => uE m (s + 8)) '' {s | s < 3}) : Set G) := by
  have hb := basisK_at (Bool.and_eq_true _ _ ▸ q5_F).1 (by norm_num)
  exact basis_tab (Gd := fun s => Q5U (Q5FG s)) (r := 3)
    (fun s hs => by rw [q5FG_eq s hs]; exact enc_uE m (by omega))
    (F_gens m).2 (F_gens m).1 hb

theorem F_eq : closure ((fun s => uE m (s + 8)) '' {s | s < 3}) = (frameOf m).F := by
  have e : (fun s => uE m (s + 8)) '' {s | s < 3} =
      {(frameOf m).a₁ * (frameOf m).a₂, (frameOf m).b₁ * (frameOf m).b₂, (frameOf m).z} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      interval_cases s
      · exact Or.inl (uE_a1a2 m)
      · exact Or.inr (Or.inl (uE_b1b2 m))
      · exact Or.inr (Or.inr (uE_z m))
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, uE_a1a2 m⟩
      · exact ⟨1, by norm_num, uE_b1b2 m⟩
      · exact ⟨2, by norm_num, uE_z m⟩
  rw [e]
  rfl

theorem card_F : Nat.card (frameOf m).F = 8 := by
  rw [← F_eq]
  exact tab_card m.inj (tabF m) (sort_inj (Bool.and_eq_true _ _ ▸ q5_F).2 (by norm_num))

theorem F_isE : IsE 3 (frameOf m).F := by
  rw [← F_eq]
  refine isE_closure ?_ ?_ (by rw [F_eq, card_F]; norm_num)
  · rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
    exact (F_gens m).2 s hs t ht
  · rintro a ⟨s, hs, rfl⟩
    exact (F_gens m).1 s hs

theorem F_inj : ∀ c < 8, ∀ d < 8,
    pwG (fun s => uE m (s + 8)) 3 c = pwG (fun s => uE m (s + 8)) 3 d → c = d := by
  intro c hc d hd h
  have hb := basisK_at (Bool.and_eq_true _ _ ▸ q5_F).1 (by norm_num)
  have hg : ∀ s < 3, Enc m.ρ (Q5U (Q5FG s)) (uE m (s + 8)) :=
    fun s hs => by rw [q5FG_eq s hs]; exact enc_uE m (by omega)
  have ec := enc_pwP m.ρ hg c
  have ed := enc_pwP m.ρ hg d
  rw [← hb c hc] at ec
  rw [← hb d hd, ← h] at ed
  exact sort_inj (Bool.and_eq_true _ _ ▸ q5_F).2 (by norm_num) c hc d hd (enc_inj ec ed)

theorem clos_tab {X Gd POS PA PB SRT SRI : ℕ → ℕ} {n k hi1 hi2 hi3 : ℕ} {g : ℕ → G}
    (hn : 0 < n) (hg : ∀ s < k, Enc m.ρ (Gd s) (g s)) (h0 : X 0 = ONEP)
    (h : (parK PA PB POS k (n - 1) hi1 && closP X Gd POS n k 0 (n * k) hi2 &&
      sortK X SRT SRI n hi3) = true)
    (h1 : n - 1 ≤ 64 * hi1) (h2 : n * k ≤ 64 * hi2) (h3 : n ≤ 64 * hi3) :
    TabOf m.ρ X n (closure (g '' {s | s < k}) : Set G) ∧
      Nat.card (closure (g '' {s | s < k})) = n ∧ ∀ i < n, ∀ j < n, X i = X j → i = j := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hp, hc⟩, hs⟩ := h
  have hcl := closP_at hc h2
  simp only [Nat.zero_add] at hcl
  have ht := tab_closure m.inj hn hg h0 hcl (parK_at hp h1)
  exact ⟨ht, tab_card m.inj ht (sort_inj hs h3), sort_inj hs h3⟩

theorem cent_closure (S : Set G) : centralizer (closure S : Set G) = centralizer S := by
  refine le_antisymm (centralizer_le subset_closure) (fun g hg => ?_)
  have hle : closure S ≤ centralizer ({g} : Set G) := (closure_le _).mpr fun s hs =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg s hs)
  exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hle hh)

theorem img_lt {f : ℕ → G} {k : ℕ} (x : G) : x ∈ f '' {s | s < k} ↔ ∃ s < k, f s = x := by
  simp

theorem S_eq : closure (uE m '' {s | s < 5}) = (frameOf m).S := by
  have e : uE m '' {s | s < 5} = {(frameOf m).a₁, (frameOf m).b₁, (frameOf m).a₂, (frameOf m).b₂,
      (frameOf m).h₀} := by
    ext x
    rw [img_lt]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [uE_gen m (by omega)]
      interval_cases s <;> simp [gen5, sGen_zero, sGen_one, sGen_two, sGen_three, sGen_four]
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_zero]⟩
      · exact ⟨1, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_one]⟩
      · exact ⟨2, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_two]⟩
      · exact ⟨3, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_three]⟩
      · exact ⟨4, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_four]⟩
  rw [e]
  rfl

theorem tabS : TabOf m.ρ Q5S 64 (closure (uE m '' {s | s < 5}) : Set G) ∧
    Nat.card (closure (uE m '' {s | s < 5})) = 64 ∧ ∀ i < 64, ∀ j < 64, Q5S i = Q5S j → i = j :=
  clos_tab m (g := uE m) (by norm_num) (fun s hs => enc_uE m (by omega))
    q5_ones.2.2.1 q5_S (by norm_num) (by norm_num) (by norm_num)

theorem card_S : Nat.card (frameOf m).S = 64 := by
  rw [← S_eq]
  exact (tabS m).2.1

theorem S_le_T5 : (frameOf m).S ≤ g23T5 m := by
  rw [← S_eq, closure_le]
  rintro x ⟨s, -, rfl⟩
  exact uE_mem m s

theorem F_le_S : (frameOf m).F ≤ (frameOf m).S :=
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab.F_le_S (frameOf m).toSFrame

@[expose] def fF (i : Fin 3) : G := uE m (i.val + 8)

theorem enc_F {c : ℕ} (hc : c < 8) : Enc m.ρ (Q5F c) (pwG (fun s => uE m (s + 8)) 3 c) := by
  have hb := basisK_at (Bool.and_eq_true _ _ ▸ q5_F).1 (by norm_num)
  have hg : ∀ s < 3, Enc m.ρ (Q5U (Q5FG s)) (uE m (s + 8)) :=
    fun s hs => by rw [q5FG_eq s hs]; exact enc_uE m (by omega)
  rw [hb c hc]
  exact enc_pwP m.ρ hg c

theorem F_range : closure (Set.range (fF m)) = (frameOf m).F := by
  rw [← F_eq]
  congr 1
  ext x
  rw [img_lt]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

theorem vecE_mem (v : Fin 3 → ZMod 2) : vecE (fF m) v ∈ (frameOf m).F := by
  rw [← F_range]
  have h : ∀ i, fF m i ∈ closure (Set.range (fF m)) := fun i => subset_closure ⟨i, rfl⟩
  exact mul_mem (mul_mem (pow_mem (h 0) _) (pow_mem (h 1) _)) (pow_mem (h 2) _)

theorem act5 {s : ℕ} (hs : s < 9) (j : Fin 3) (hMG : Q5MG s < 34) :
    uE m (Q5MG s) * fF m j * (uE m (Q5MG s))⁻¹ = vecE (fF m) (fun i => m9 (Q5M s) i j) := by
  have h := actK_at q5_act (by norm_num) s hs j.val j.2
  have hcol : (Q5M s >>> (3 * j.val)) &&& 7 < 8 := Nat.lt_succ_of_le Nat.and_le_right
  have e2 : pwG (fun s => uE m (s + 8)) 3 (2 ^ j.val) = fF m j := pwG_two_pow j.2
  have h' := mul_eq_of_MULP m.inj (enc_uE m hMG) (enc_F m (c := 2 ^ j.val)
    (by have := j.2; interval_cases (j.val) <;> norm_num)) (enc_F m hcol) (enc_uE m hMG) h
  rw [e2] at h'
  rw [h', mul_inv_cancel_right]
  exact pwG_col (fun s => uE m (s + 8)) (Q5M s) j

theorem q5MG_eq : ∀ s < 9, Q5MG s = [11, 14, 0, 15, 5, 17, 1, 2, 3].getD s 0 := by
  intro s hs
  interval_cases s
  all_goals exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem norm_F {s : ℕ} (hs : s < 9) : uE m (Q5MG s) ∈ normalizer ((frameOf m).F : Set G) := by
  have hMG : Q5MG s < 34 := by
    rw [q5MG_eq s hs]
    interval_cases s <;> norm_num
  have hle : closure ({uE m (Q5MG s)} : Set G) ≤ normalizer ((frameOf m).F : Set G) := by
    rw [← F_range]
    refine closure_le_normalizer ?_
    intro g hg t ht
    rw [Set.mem_singleton_iff] at hg
    obtain ⟨j, hj⟩ := ht
    rw [hg, ← hj, act5 m hs j hMG, F_range]
    exact vecE_mem m _
  exact hle (subset_closure rfl)

theorem T5_le_norm_F : g23T5 m ≤ normalizer ((frameOf m).F : Set G) := by
  rw [← T5_eq, closure_le]
  rintro x ⟨s, hs, rfl⟩
  have hs' : s = 0 ∨ s = 1 := by simp at hs; omega
  rcases hs' with rfl | rfl
  · have := norm_F m (s := 0) (by norm_num)
    rwa [q5MG_eq 0 (by norm_num)] at this
  · have := norm_F m (s := 1) (by norm_num)
    rwa [q5MG_eq 1 (by norm_num)] at this

theorem F_le_T5 : (frameOf m).F ≤ g23T5 m := (F_le_S m).trans (S_le_T5 m)

theorem F_normal : ((frameOf m).F.subgroupOf (g23T5 m)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (F_le_T5 m)).mpr (T5_le_norm_F m)

theorem F_GL3 : SecProp (g23T5 m) (frameOf m).F
    (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
  have hgl := q5_gl
  simp only [Bool.and_eq_true] at hgl
  obtain ⟨⟨hp, hc⟩, hs⟩ := hgl
  have h168 := clos9_card (Gd := Q5M) (n := 168) (k := 2) (by norm_num) q5_ones.2.2.2.2.2.2.2.2.1
    (clos9_at hc (by norm_num)) (parK_at hp (by norm_num)) (sort_inj hs (by norm_num))
  refine secProp_gl3 (fF m) (fun i j => (F_gens m).2 _ i.2 _ j.2) (fun i => (F_gens m).1 _ i.2)
    (F_range m).symm (card_F m) (F_le_T5 m) (T5_le_norm_F m) (card_T5 m)
    (fun s : Fin 2 => uE m (Q5MG s)) (fun s => uE_mem m _) (fun s : Fin 2 => m9 (Q5M s))
    (fun s j => act5 m (by omega) j (by
      have := s.2
      rw [q5MG_eq s (by omega)]
      interval_cases (s : ℕ) <;> norm_num)) h168

theorem S_sylow : IsSylowIn 2 (g23T5 m) (frameOf m).S := by
  refine ⟨S_le_T5 m, IsPGroup.of_card (n := 6) (by rw [card_S]; norm_num), ?_⟩
  have h := relIndex_mul_card (H := (frameOf m).S) (K := g23T5 m)
  rw [inf_of_le_left (S_le_T5 m), card_S, card_T5] at h
  have h21 : (frameOf m).S.relIndex (g23T5 m) = 21 := by omega
  rw [h21]
  norm_num

theorem tabF' : TabOf m.ρ Q5F 8 ((frameOf m).F : Set G) := by
  rw [← F_eq]
  exact tabF m

theorem S_no_complement : ∀ P : Subgroup G, P ≤ (frameOf m).S → P ⊓ (frameOf m).F = ⊥ →
    Nat.card P * Nat.card (frameOf m).F ≠ Nat.card (frameOf m).S := by
  have hq := q5_sq
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨hsq, hlt⟩, hne⟩ := hq
  have hS : TabOf m.ρ Q5S 64 ((frameOf m).S : Set G) := by
    rw [← S_eq]
    exact (tabS m).1
  have hlt' := ltK_at hlt (by norm_num) 0 (by norm_num)
  obtain ⟨x, hxS, hx⟩ := hS.1 _ hlt'
  refine no_complement (F_le_S m) ((S_le_T5 m).trans (T5_le_norm_F m)) (card_S m) (card_F m)
    (sqInK_sound m.inj hsq (by norm_num) hS (tabF' m)) hxS ?_
  intro hx2
  obtain ⟨q, hq8, hqx⟩ := (tabF' m).2 _ hx2
  have h := neK_at hne (by norm_num) q hq8
  refine mul_ne_of_MULP hx hx hqx (q5_ones.1 ▸ enc_one m.ρ) h ?_
  rw [pow_two, mul_one]

theorem uE_mem_S {s : ℕ} (hs : s < 5) : uE m s ∈ (frameOf m).S := by
  rw [← S_eq]
  exact subset_closure ⟨s, hs, rfl⟩

theorem uE_mem_F {s : ℕ} (hs : s < 3) : uE m (s + 8) ∈ (frameOf m).F := by
  rw [← F_eq]
  exact subset_closure ⟨s, hs, rfl⟩

theorem B_eq_cent : (frameOf m).B = (frameOf m).S ⊓ centralizer ({uE m 9} : Set G) := by
  have e : (frameOf m).B = centIn (frameOf m).S (closure {(frameOf m).b₁ * (frameOf m).b₂}) := rfl
  rw [e, centIn, cent_closure, uE_b1b2]

theorem card_B : Nat.card (frameOf m).B = 32 := by
  have h := cntK_card m.inj (tabS m).1 (tabS m).2.2 (g := fun _ => uE m 9) (k := 1) (hi := 1)
    (fun _ _ => enc_uE m (by norm_num)) (by norm_num)
  have e : (fun _ => uE m 9) '' {s : ℕ | s < 1} = {uE m 9} := by
    ext x
    simp [eq_comm]
  rw [e, S_eq, Nat.eq_of_beq_eq_true q5_cntB] at h
  rw [B_eq_cent, ← h]

theorem q5BG_eq : Q5BG 0 = 1 ∧ Q5BG 1 = 3 ∧ Q5BG 2 = 4 ∧ Q5BG 3 = 8 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem q5BG_lt : ∀ s < 4, Q5BG s < 34 := by
  intro s hs
  obtain ⟨h0, h1, h2, h3⟩ := q5BG_eq
  interval_cases s <;> simp [h0, h1, h2, h3]

@[expose] noncomputable def gB (s : ℕ) : G := uE m (Q5BG s)

theorem tabB : TabOf m.ρ Q5B 32 (closure (gB m '' {s | s < 4}) : Set G) ∧
    Nat.card (closure (gB m '' {s | s < 4})) = 32 ∧ ∀ i < 32, ∀ j < 32, Q5B i = Q5B j → i = j :=
  clos_tab m (Gd := fun s => Q5U (Q5BG s)) (g := gB m) (by norm_num)
    (fun s hs => enc_uE m (q5BG_lt s hs)) q5_ones.2.2.2.2.1 q5_B (by norm_num) (by norm_num)
    (by norm_num)

theorem ZB_comm : ∀ s < 4, uE m 9 * gB m s = gB m s * uE m 9 ∧
    uE m 10 * gB m s = gB m s * uE m 10 := by
  obtain ⟨h0, h1, h2, h3⟩ := q5BG_eq
  intro s hs
  interval_cases s <;> simp only [gB, h0, h1, h2, h3]
  · exact ⟨(rl m 40 1 9 9 1 (by quickRfl)).symm, rl m 42 10 1 1 10 (by quickRfl)⟩
  · exact ⟨(rl m 41 3 9 9 3 (by quickRfl)).symm, rl m 43 10 3 3 10 (by quickRfl)⟩
  · exact ⟨rl m 38 9 4 4 9 (by quickRfl), rl m 39 10 4 4 10 (by quickRfl)⟩
  · exact ⟨(rl m 31 8 9 9 8 (by quickRfl)).symm, (rl m 32 8 10 10 8 (by quickRfl)).symm⟩

theorem gB_mem_B : ∀ s < 4, gB m s ∈ (frameOf m).B := by
  obtain ⟨h0, h1, h2, h3⟩ := q5BG_eq
  intro s hs
  rw [B_eq_cent]
  refine ⟨?_, mem_centralizer_singleton_iff.mpr (ZB_comm m s hs).1.symm⟩
  interval_cases s <;> simp only [gB, h0, h1, h2, h3]
  · exact uE_mem_S m (by norm_num)
  · exact uE_mem_S m (by norm_num)
  · exact uE_mem_S m (by norm_num)
  · exact F_le_S m (uE_mem_F m (s := 0) (by norm_num))

theorem B_eq : closure (gB m '' {s | s < 4}) = (frameOf m).B := by
  refine Subgroup.eq_of_le_of_card_ge ((closure_le _).mpr ?_) (by rw [card_B, (tabB m).2.1])
  rintro x ⟨s, hs, rfl⟩
  exact gB_mem_B m s hs

theorem cen_B_eq_cent : cen (frameOf m).B = (frameOf m).B ⊓ centralizer (gB m '' {s | s < 4}) := by
  rw [cen]
  congr 1
  rw [← B_eq, cent_closure]

theorem card_cen_B : Nat.card (cen (frameOf m).B) = 4 := by
  have h := cntK_card m.inj (tabB m).1 (tabB m).2.2 (Gd := fun s => Q5U (Q5BG s)) (g := gB m)
    (k := 4) (hi := 1) (fun s hs => enc_uE m (q5BG_lt s hs)) (by norm_num)
  rw [B_eq, Nat.eq_of_beq_eq_true q5_cntZB] at h
  rw [cen_B_eq_cent, ← h]

theorem cen_B_uE : cen (frameOf m).B = closure {uE m 9, uE m 10} := by
  have hle : closure {uE m 9, uE m 10} ≤ cen (frameOf m).B := by
    rw [closure_le, cen_B_eq_cent]
    intro x hx
    obtain hx | hx := hx
    · rw [hx]
      refine ⟨?_, ?_⟩
      · rw [B_eq_cent]
        exact ⟨F_le_S m (uE_mem_F m (s := 1) (by norm_num)), mem_centralizer_singleton_iff.mpr rfl⟩
      · refine mem_centralizer_iff.mpr ?_
        rintro y ⟨s, hs, rfl⟩
        exact (ZB_comm m s hs).1.symm
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨?_, ?_⟩
      · rw [B_eq_cent]
        exact ⟨F_le_S m (uE_mem_F m (s := 2) (by norm_num)),
          mem_centralizer_singleton_iff.mpr (rl m 33 9 10 10 9 (by quickRfl)).symm⟩
      · refine mem_centralizer_iff.mpr ?_
        rintro y ⟨s, hs, rfl⟩
        exact (ZB_comm m s hs).2.symm
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_cen_B]
  let g : ℕ → G := fun s => uE m (s + 8)
  have p0 : pwG g 3 0 = 1 := by
    simp [pwG]
    rfl
  have p2 : pwG g 3 2 = uE m 9 := pwG_two_pow (j := 1) (by norm_num)
  have p4 : pwG g 3 4 = uE m 10 := pwG_two_pow (j := 2) (by norm_num)
  have p6 : pwG g 3 6 = uE m 9 * uE m 10 := by
    rw [← p2, ← p4, pwG_mul (F_gens m).2 (F_gens m).1]
    rfl
  let v : Fin 4 → closure ({uE m 9, uE m 10} : Set G) := fun i =>
    ⟨pwG g 3 (2 * i.val), by
      fin_cases i
      · simp only [Fin.val_zero, Nat.mul_zero, p0]
        exact one_mem _
      · simp only [Fin.mk_one, Fin.val_one, Nat.mul_one, p2]
        exact subset_closure (by simp)
      · simp only [show 2 * (⟨2, by norm_num⟩ : Fin 4).val = 4 from rfl, p4]
        exact subset_closure (by simp)
      · simp only [show 2 * (⟨3, by norm_num⟩ : Fin 4).val = 6 from rfl, p6]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))⟩
  have hv : Function.Injective v := by
    intro i j hij
    have h := F_inj m (2 * i.val) (by omega) (2 * j.val) (by omega)
      (congrArg Subtype.val hij)
    exact Fin.ext (by omega)
  have := Nat.card_le_card_of_injective v hv
  simpa using this

theorem cen_B : cen (frameOf m).B = closure {(frameOf m).b₁ * (frameOf m).b₂, (frameOf m).z} := by
  rw [cen_B_uE, uE_b1b2, uE_z]

theorem cen_B_isE : IsE 2 (cen (frameOf m).B) := by
  rw [cen_B_uE]
  have h4 : Nat.card (closure ({uE m 9, uE m 10} : Set G)) = 2 ^ 2 := by
    rw [← cen_B_uE, card_cen_B]
    norm_num
  have c := (F_gens m).2 1 (by norm_num) 2 (by norm_num)
  have i9 := (F_gens m).1 1 (by norm_num)
  have i10 := (F_gens m).1 2 (by norm_num)
  refine isE_closure ?_ ?_ h4
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    exacts [c, c.symm]
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha <;> rw [ha]
    exacts [i9, i10]

theorem q5PG_eq : Q5PG 0 = 0 ∧ Q5PG 1 = 15 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem q5PG_lt : ∀ s < 2, Q5PG s < 34 := by
  intro s hs
  interval_cases s <;> simp [q5PG_eq.1, q5PG_eq.2]

@[expose] noncomputable def gP (s : ℕ) : G := uE m (Q5PG s)

theorem tabP : TabOf m.ρ Q5P 192 (closure (gP m '' {s | s < 2}) : Set G) ∧
    Nat.card (closure (gP m '' {s | s < 2})) = 192 ∧ ∀ i < 192, ∀ j < 192, Q5P i = Q5P j → i = j :=
  clos_tab m (Gd := fun s => Q5U (Q5PG s)) (g := gP m) (by norm_num)
    (fun s hs => enc_uE m (q5PG_lt s hs)) q5_ones.2.2.2.2.2.1 q5_P (by norm_num) (by norm_num)
    (by norm_num)

theorem P_le_norm_B : closure (gP m '' {s | s < 2}) ≤ normalizer ((frameOf m).B : Set G) := by
  have hq := q5_normB
  simp only [Bool.and_eq_true] at hq
  rw [← B_eq]
  refine closure_le_normalizer ?_
  rintro p ⟨a, ha, rfl⟩ b ⟨c, hc, rfl⟩
  have h : MULP (Q5U (Q5PG ((4 * a + c) / 4))) (Q5U (Q5BG ((4 * a + c) % 4))) =
      MULP (Q5B (Q5NBW (4 * a + c))) (Q5U (Q5PG ((4 * a + c) / 4))) :=
    eqK_at hq.1 (by norm_num) (4 * a + c) (by simp at ha hc; omega)
  have e1 : (4 * a + c) / 4 = a := by simp at hc; omega
  have e2 : (4 * a + c) % 4 = c := by simp at hc; omega
  rw [e1, e2] at h
  have hl := ltK_at hq.2 (by norm_num) (4 * a + c) (by simp at ha hc; omega)
  obtain ⟨x, hx, hxe⟩ := (tabB m).1.1 _ hl
  have e := mul_eq_of_MULP m.inj (enc_uE m (q5PG_lt a ha)) (enc_uE m (q5BG_lt c hc)) hxe
    (enc_uE m (q5PG_lt a ha)) h
  have e' : gP m a * gB m c * (gP m a)⁻¹ = x := by
    rw [gP, gB, e, mul_inv_cancel_right]
  rw [e']
  exact hx

theorem P_le : closure (gP m '' {s | s < 2}) ≤ normIn (g23T5 m) (frameOf m).B := by
  refine le_inf ((closure_le _).mpr ?_) (P_le_norm_B m)
  rintro x ⟨s, -, rfl⟩
  exact uE_mem m _

@[expose] noncomputable def cB (i : Fin 7) : G := uE m (Q5CBU (2 * i.val))

theorem q5CB : ∀ i < 7, Q5CBU (2 * i + 1) = Q5CBU (2 * i) ∧ Q5CBV (2 * i) = 9 ∧
    Q5CBV (2 * i + 1) = 10 ∧ Q5CBU (2 * i) < 34 := by
  intro i hi
  interval_cases i
  all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), by decide⟩

theorem q5P7 : ∀ j < 7, ∀ i < j, Q5P7I (j * (j - 1) / 2 + i) = i ∧
    Q5P7J (j * (j - 1) / 2 + i) = j := by
  intro j hj i hi
  interval_cases j <;> interval_cases i
  all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem conjSub_pair (c a b : G) :
    conjSub c (closure {a, b}) = closure {c * a * c⁻¹, c * b * c⁻¹} := by
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem cB_conj (i : Fin 7) : conjSub (cB m i) (cen (frameOf m).B) =
    closure {pwG (fun s => uE m (s + 8)) 3 (Q5CBW (2 * i.val)),
      pwG (fun s => uE m (s + 8)) 3 (Q5CBW (2 * i.val + 1))} := by
  have hq := q5_conjB
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨he, hl⟩, -⟩ := hq
  obtain ⟨h1, h2, h3, h4⟩ := q5CB i.val i.2
  have conj : ∀ q < 14, Q5CBU q = Q5CBU (2 * i.val) → ∀ v, Q5CBV q = v → v < 34 →
      cB m i * uE m v * (cB m i)⁻¹ = pwG (fun s => uE m (s + 8)) 3 (Q5CBW q) := by
    intro q hq hu v hv hv34
    have h := eqK_at he (by norm_num) q hq
    rw [hu, hv] at h
    have hw := ltK_at hl (by norm_num) q hq
    have e := mul_eq_of_MULP m.inj (enc_uE m h4) (enc_uE m hv34) (enc_F m hw) (enc_uE m h4) h
    rw [cB, e, mul_inv_cancel_right]
  rw [cen_B_uE, conjSub_pair, conj (2 * i.val) (by omega) rfl 9 h2 (by norm_num),
    conj (2 * i.val + 1) (by omega) h1 10 h3 (by norm_num)]

theorem cB_ne {i j : Fin 7} (hij : i.val < j.val) :
    conjSub (cB m i) (cen (frameOf m).B) ≠ conjSub (cB m j) (cen (frameOf m).B) := by
  have hq := q5_conjB
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨-, hl⟩, hn⟩ := hq
  obtain ⟨hpi, hpj⟩ := q5P7 j.val j.2 i.val hij
  have hne := neqK_at hn (by norm_num) (j.val * (j.val - 1) / 2 + i.val) (by
    have := j.2
    interval_cases (j : ℕ) <;> omega)
  simp only [hpi, hpj] at hne
  rw [cB_conj, cB_conj]
  exact closure_pair_ne (F_gens m).2 (F_gens m).1 (F_inj m)
    (ltK_at hl (by norm_num) _ (by omega)) (ltK_at hl (by norm_num) _ (by omega))
    (ltK_at hl (by norm_num) _ (by omega)) (ltK_at hl (by norm_num) _ (by omega)) hne

theorem P_eq : closure (gP m '' {s | s < 2}) = normIn (g23T5 m) (frameOf m).B := by
  refine Subgroup.eq_of_le_of_card_ge (P_le m) ?_
  rw [(tabP m).2.1]
  have h7 := card_mul_card_normIn_le (T := g23T5 m) (H := cen (frameOf m).B) (cB m)
    (fun i => uE_mem m _) (fun i j h => by
      by_contra hne
      rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne (Fin.ext e)) with hl | hl
      · exact cB_ne m hl h
      · exact cB_ne m hl h.symm)
  rw [card_T5] at h7
  have hle : normIn (g23T5 m) (frameOf m).B ≤ normIn (g23T5 m) (cen (frameOf m).B) :=
    normIn_le_normIn_cen
  have := Subgroup.card_le_of_le hle
  omega

theorem card_normIn_B : Nat.card (normIn (g23T5 m) (frameOf m).B) = 192 := by
  rw [← P_eq]
  exact (tabP m).2.1

theorem basis3 {X Gd SRT SRI : ℕ → ℕ} (hG : ∀ s < 3, Gd s < 34)
    (hc : ∀ s < 3, ∀ t < 3, uE m (Gd s) * uE m (Gd t) = uE m (Gd t) * uE m (Gd s))
    (hs : ∀ s < 3, uE m (Gd s) * uE m (Gd s) = 1)
    (h : (basisK X (fun s => Q5U (Gd s)) 3 8 1 && sortK X SRT SRI 8 1) = true) :
    TabOf m.ρ X 8 (closure ((fun s => uE m (Gd s)) '' {s | s < 3}) : Set G) ∧
      Nat.card (closure ((fun s => uE m (Gd s)) '' {s | s < 3})) = 8 ∧
      ∀ c < 8, Enc m.ρ (X c) (pwG (fun s => uE m (Gd s)) 3 c) := by
  simp only [Bool.and_eq_true] at h
  have hb := basisK_at h.1 (by norm_num)
  have hg : ∀ s < 3, Enc m.ρ (Q5U (Gd s)) (uE m (Gd s)) := fun s hs' => enc_uE m (hG s hs')
  have ht := basis_tab (Gd := fun s => Q5U (Gd s)) hg hc hs hb
  refine ⟨ht, tab_card m.inj ht (sort_inj h.2 (by norm_num)), fun c hc8 => ?_⟩
  rw [hb c hc8]
  exact enc_pwP m.ρ hg c

theorem gens3 {Gd : ℕ → ℕ} {a b c : ℕ} (h0 : Gd 0 = a) (h1 : Gd 1 = b) (h2 : Gd 2 = c)
    (ia : uE m a * uE m a = 1) (ib : uE m b * uE m b = 1) (ic : uE m c * uE m c = 1)
    (cab : uE m a * uE m b = uE m b * uE m a) (cac : uE m a * uE m c = uE m c * uE m a)
    (cbc : uE m b * uE m c = uE m c * uE m b) :
    (∀ s < 3, ∀ t < 3, uE m (Gd s) * uE m (Gd t) = uE m (Gd t) * uE m (Gd s)) ∧
      ∀ s < 3, uE m (Gd s) * uE m (Gd s) = 1 := by
  refine ⟨fun s hs t ht => ?_, fun s hs => ?_⟩
  · interval_cases s <;> interval_cases t
    · rfl
    · rw [h0, h1]; exact cab
    · rw [h0, h2]; exact cac
    · rw [h0, h1]; exact cab.symm
    · rfl
    · rw [h1, h2]; exact cbc
    · rw [h0, h2]; exact cac.symm
    · rw [h1, h2]; exact cbc.symm
    · rfl
  · interval_cases s
    · rw [h0]; exact ia
    · rw [h1]; exact ib
    · rw [h2]; exact ic

theorem i1 (a : ℕ) (q : ℕ) (h : (Nat.beq (Q5RA q) a && Nat.beq (Q5RB q) a && Nat.beq (Q5RC q) 7 &&
    Nat.beq (Q5RD q) 7 && Nat.blt q 48 && Nat.blt a 34 && Nat.blt a 34 && Nat.blt 7 34 &&
    Nat.blt 7 34) = true) : uE m a * uE m a = 1 := by
  have := rl m q a a 7 7 h
  rwa [uE_seven, mul_one] at this

theorem q5EG : Q5EG 0 = 9 ∧ Q5EG 1 = 12 ∧ Q5EG 2 = 10 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem q5YG : Q5YG 0 = 9 ∧ Q5YG 1 = 10 ∧ Q5YG 2 = 4 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem lt34 {Gd : ℕ → ℕ} {a b c : ℕ} (h0 : Gd 0 = a) (h1 : Gd 1 = b) (h2 : Gd 2 = c)
    (h : a < 34 ∧ b < 34 ∧ c < 34) : ∀ s < 3, Gd s < 34 := by
  intro s hs
  interval_cases s <;> simp only [h0, h1, h2] <;> omega

theorem tabE : TabOf m.ρ Q5E 8 (closure ((fun s => uE m (Q5EG s)) '' {s | s < 3}) : Set G) ∧
    Nat.card (closure ((fun s => uE m (Q5EG s)) '' {s | s < 3})) = 8 ∧
    ∀ c < 8, Enc m.ρ (Q5E c) (pwG (fun s => uE m (Q5EG s)) 3 c) := by
  have hg := gens3 m q5EG.1 q5EG.2.1 q5EG.2.2 (i1 m 9 29 (by quickRfl))
    (i1 m 12 34 (by quickRfl)) (i1 m 10 30 (by quickRfl)) (rl m 35 9 12 12 9 (by quickRfl))
    (rl m 33 9 10 10 9 (by quickRfl)) (rl m 36 12 10 10 12 (by quickRfl))
  exact basis3 m (lt34 q5EG.1 q5EG.2.1 q5EG.2.2 (by norm_num)) hg.1 hg.2 q5_E

theorem tabY : TabOf m.ρ Q5Y 8 (closure ((fun s => uE m (Q5YG s)) '' {s | s < 3}) : Set G) ∧
    Nat.card (closure ((fun s => uE m (Q5YG s)) '' {s | s < 3})) = 8 ∧
    ∀ c < 8, Enc m.ρ (Q5Y c) (pwG (fun s => uE m (Q5YG s)) 3 c) := by
  have hg := gens3 m q5YG.1 q5YG.2.1 q5YG.2.2 (i1 m 9 29 (by quickRfl))
    (i1 m 10 30 (by quickRfl)) (i1 m 4 37 (by quickRfl)) (rl m 33 9 10 10 9 (by quickRfl))
    (rl m 38 9 4 4 9 (by quickRfl)) (rl m 39 10 4 4 10 (by quickRfl))
  exact basis3 m (lt34 q5YG.1 q5YG.2.1 q5YG.2.2 (by norm_num)) hg.1 hg.2 q5_Y

theorem shl1 (n : ℕ) : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n

theorem image3 {f : ℕ → G} {a b c : G} (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) :
    f '' {s | s < 3} = {a, b, c} := by
  ext x
  rw [img_lt]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, hx⟩
    interval_cases s
    · exact Or.inl (hx.symm.trans h0)
    · exact Or.inr (Or.inl (hx.symm.trans h1))
    · exact Or.inr (Or.inr (hx.symm.trans h2))
  · rintro (hx | hx | hx)
    · exact ⟨0, by norm_num, h0.trans hx.symm⟩
    · exact ⟨1, by norm_num, h1.trans hx.symm⟩
    · exact ⟨2, by norm_num, h2.trans hx.symm⟩

theorem uE_h0 : uE m 4 = (frameOf m).h₀ := by
  rw [uE_gen m (by norm_num)]
  simp [gen5, sGen_four]

theorem uE_a1b1a2 : uE m 12 = (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂ := by
  have h11 := rl m 3 0 1 11 7 (by quickRfl)
  have h12 := rl m 4 11 2 12 7 (by quickRfl)
  rw [uE_seven, mul_one] at h11 h12
  rw [← h12, ← h11, uE_gen m (by norm_num), uE_gen m (by norm_num), uE_gen m (by norm_num)]
  simp [gen5, sGen_zero, sGen_one, sGen_two]

theorem E_eq : closure ((fun s => uE m (Q5EG s)) '' {s | s < 3}) = (frameOf m).E := by
  have h0 : uE m (Q5EG 0) = (frameOf m).b₁ * (frameOf m).b₂ := by rw [q5EG.1, uE_b1b2]
  have h1 : uE m (Q5EG 1) = (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂ := by
    rw [q5EG.2.1, uE_a1b1a2]
  have h2 : uE m (Q5EG 2) = (frameOf m).z := by rw [q5EG.2.2, uE_z]
  rw [image3 (f := fun s => uE m (Q5EG s)) h0 h1 h2]
  rfl

theorem Y_eq : closure ((fun s => uE m (Q5YG s)) '' {s | s < 3}) =
    cen (frameOf m).B ⊔ closure {(frameOf m).h₀} := by
  have h0 : uE m (Q5YG 0) = uE m 9 := by rw [q5YG.1]
  have h1 : uE m (Q5YG 1) = uE m 10 := by rw [q5YG.2.1]
  have h2 : uE m (Q5YG 2) = (frameOf m).h₀ := by rw [q5YG.2.2, uE_h0]
  rw [image3 (f := fun s => uE m (Q5YG s)) h0 h1 h2, cen_B_uE, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem Y1_conj : ∃ t ∈ g23T5 m,
    cen (frameOf m).B ⊔ closure {(frameOf m).h₀} = conjSub t (frameOf m).E := by
  refine ⟨uE m 24, uE_mem m 24, ?_⟩
  rw [← Y_eq, ← E_eq]
  refine (conjSub_eq_of_gens rfl ?_ (by rw [(tabE m).2.1, (tabY m).2.1])).symm
  have hq := q5_f19
  simp only [Bool.and_eq_true] at hq
  rintro x ⟨s, hs, rfl⟩
  have hs' : s < 3 := hs
  have h : MULP (Q5U 24) (Q5E (Nat.shiftLeft 1 s)) = MULP (Q5Y (Q5YW s)) (Q5U 24) :=
    eqK_at hq.1 (by norm_num) s hs'
  rw [shl1] at h
  have hw := ltK_at hq.2 (by norm_num) s hs'
  have he := (tabE m).2.2 (2 ^ s) (by interval_cases s <;> norm_num)
  rw [pwG_two_pow hs'] at he
  have e := mul_eq_of_MULP m.inj (enc_uE m (by norm_num)) he ((tabY m).2.2 _ hw)
    (enc_uE m (by norm_num)) h
  rw [e, mul_inv_cancel_right]
  exact mem_of_tabOf m.inj (tabY m).1 hw ((tabY m).2.2 _ hw)

theorem q5CE_lt : ∀ i < 9, Q5CE i < 34 := by
  intro i hi
  interval_cases i
  all_goals decide

theorem q5ED : ∀ j < 9, ∀ i < j, Q5EDI (j * (j - 1) / 2 + i) = Q5CE i ∧
    Q5EDJ (j * (j - 1) / 2 + i) = Q5CE j := by
  intro j hj i hi
  interval_cases j <;> interval_cases i
  all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem tabE' : TabOf m.ρ Q5E 8 ((frameOf m).E : Set G) := by
  rw [← E_eq]
  exact (tabE m).1

theorem nine_ne {i j : ℕ} (hj : j < 9) (hij : i < j) :
    conjSub (uE m (Q5CE i)) (frameOf m).E ≠ conjSub (uE m (Q5CE j)) (frameOf m).E := by
  have hq := q5_nine
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨-, -⟩, hed⟩, hdd⟩, hdw⟩ := hq
  set q := j * (j - 1) / 2 + i with hqdef
  have hq36 : q < 36 := by interval_cases j <;> omega
  obtain ⟨hI, hJ⟩ := q5ED j hj i hij
  have h : MULP (Q5U (Q5EDJ q)) (Q5X (Q5EDD q)) = MULP (Q5U (Q5EDI q)) (Q5U 7) :=
    eqK_at hed (by norm_num) q hq36
  rw [hI, hJ, q5_ones.1] at h
  have hd : Q5EDD q < 1344 := ltK_at hdd (by norm_num) q hq36
  obtain ⟨d, -, hdE⟩ := (tabX m).1 _ hd
  have e := mul_eq_of_MULP m.inj (enc_uE m (q5CE_lt j hj)) hdE (enc_uE m (q5CE_lt i (by omega)))
    (enc_one m.ρ) h
  rw [mul_one] at e
  have hw : Q5EDW q < 3 := ltK_at hdw (by norm_num) q hq36
  have hwe := (tabE m).2.2 (2 ^ Q5EDW q) (by
    have : 2 ^ Q5EDW q ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  rw [pwG_two_pow hw] at hwe
  refine conjSub_ne_of_witness (e := uE m (Q5EG (Q5EDW q))) e ?_ ?_
  · rw [← E_eq]
    exact subset_closure ⟨_, hw, rfl⟩
  · intro e' he'
    obtain ⟨k, hk, hke⟩ := (tabE' m).2 e' he'
    have hn : MULP (Q5X (Q5EDD ((8 * q + k) / 8))) (Q5E (Nat.shiftLeft 1 (Q5EDW ((8 * q + k) / 8))))
        ≠ MULP (Q5E ((8 * q + k) % 8)) (Q5X (Q5EDD ((8 * q + k) / 8))) :=
      neK_at q5_nineW (by norm_num) (8 * q + k) (by omega)
    have e1 : (8 * q + k) / 8 = q := by omega
    have e2 : (8 * q + k) % 8 = k := by omega
    rw [e1, e2, shl1] at hn
    exact mul_ne_of_MULP hdE hwe hke hdE hn

theorem nine_conj_E : ∃ Ws : List (Subgroup G), Ws.Nodup ∧ Ws.length = 9 ∧
    ∀ W ∈ Ws, (∃ t ∈ g23T5 m, W = conjSub t (frameOf m).E) ∧ (frameOf m).z ∈ W := by
  refine ⟨List.ofFn fun i : Fin 9 => conjSub (uE m (Q5CE i)) (frameOf m).E, ?_, by simp, ?_⟩
  · refine List.nodup_ofFn.mpr fun i j h => ?_
    by_contra hne
    rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne (Fin.ext e)) with hl | hl
    · exact nine_ne m j.2 hl h
    · exact nine_ne m i.2 hl h.symm
  · intro W hW
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW
    refine ⟨⟨_, uE_mem m _, rfl⟩, ?_⟩
    have hq := q5_nine
    simp only [Bool.and_eq_true] at hq
    obtain ⟨⟨⟨⟨hz, hl⟩, -⟩, -⟩, -⟩ := hq
    have h : MULP (Q5U (Q5CE i)) (Q5E (Q5CEW i)) = MULP (Q5U 10) (Q5U (Q5CE i)) :=
      eqK_at hz (by norm_num) i i.2
    have hw : Q5CEW i < 8 := ltK_at hl (by norm_num) i i.2
    obtain ⟨e, heE, hee⟩ := (tabE' m).1 _ hw
    have e1 := mul_eq_of_MULP m.inj (enc_uE m (q5CE_lt i i.2)) hee (enc_uE m (by norm_num))
      (enc_uE m (q5CE_lt i i.2)) h
    rw [uE_z] at e1
    exact mem_conjSub_of heE e1

theorem eq_of_card4 {K : Subgroup G} (hK : Nat.card K = 4) (v : Fin 4 → G)
    (hv : Function.Injective v) (hvK : ∀ i, v i ∈ K) {y : G} (hy : y ∈ K) : ∃ i, y = v i := by
  by_contra h
  simp only [not_exists] at h
  let f : Option (Fin 4) → K := fun o => match o with
    | none => ⟨y, hy⟩
    | some i => ⟨v i, hvK i⟩
  have hf : Function.Injective f := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd (congrArg Subtype.val hij) (h j)
    · exact absurd (congrArg Subtype.val hij).symm (h i)
    · exact congrArg some (hv (congrArg Subtype.val hij))
  have := Nat.card_le_card_of_injective f hf
  have h5 : Nat.card (Option (Fin 4)) = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
  rw [h5, hK] at this
  omega

@[expose] noncomputable def vZ (i : Fin 4) : G := ![1, uE m 9, uE m 10, uE m 23] i

theorem vZ_pw (i : Fin 4) : vZ m i = pwG (fun s => uE m (s + 8)) 3 (2 * i.val) := by
  have p2 : pwG (fun s => uE m (s + 8)) 3 2 = uE m 9 := pwG_two_pow (j := 1) (by norm_num)
  have p4 : pwG (fun s => uE m (s + 8)) 3 4 = uE m 10 := pwG_two_pow (j := 2) (by norm_num)
  have h23 := rl m 15 9 10 23 7 (by quickRfl)
  rw [uE_seven, mul_one] at h23
  fin_cases i
  · simp [vZ, pwG]
    rfl
  · simp [vZ, p2]
  · simp [vZ, p4]
  · simp only [vZ]
    rw [← h23, ← p2, ← p4, pwG_mul (F_gens m).2 (F_gens m).1]
    rfl

theorem vZ_inj : Function.Injective (vZ m) := by
  intro i j h
  rw [vZ_pw, vZ_pw] at h
  have := F_inj m _ (by omega) _ (by omega) h
  exact Fin.ext (by omega)

theorem vZ_mem (i : Fin 4) : vZ m i ∈ cen (frameOf m).B := by
  rw [cen_B_uE]
  have h23 := rl m 15 9 10 23 7 (by quickRfl)
  rw [uE_seven, mul_one] at h23
  fin_cases i
  · exact one_mem _
  · exact subset_closure (by simp [vZ])
  · exact subset_closure (by simp [vZ])
  · simp only [vZ]
    rw [← h23]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem nrl (q a b c d : ℕ) (h : (Nat.beq (Q5NA q) a && Nat.beq (Q5NB q) b && Nat.beq (Q5NC q) c &&
    Nat.beq (Q5ND q) d && Nat.blt q 5 && Nat.blt a 34 && Nat.blt b 34 && Nat.blt c 34 &&
    Nat.blt d 34) = true) : uE m a * uE m b ≠ uE m c * uE m d := by
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hq⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  have hn : MULP (Q5U (Q5NA q)) (Q5U (Q5NB q)) ≠ MULP (Q5U (Q5NC q)) (Q5U (Q5ND q)) :=
    neK_at q5_nrel (by norm_num) q hq
  rw [ha, hb, hc, hd] at hn
  exact mul_ne_of_MULP (enc_uE m h1) (enc_uE m h2) (enc_uE m h3) (enc_uE m h4) hn

theorem tau_mem_P : uE m 20 ∈ normIn (g23T5 m) (frameOf m).B := by
  rw [← P_eq]
  have h := idxK_at q5_tauP (by norm_num) 0 (by norm_num)
  have he : Enc m.ρ (Q5P (Q5TP 0)) (uE m 20) := by
    rw [h.2]
    exact enc_uE m (by norm_num)
  exact mem_of_tabOf m.inj (tabP m).1 h.1 he

theorem a1_mem_P : uE m 0 ∈ normIn (g23T5 m) (frameOf m).B := by
  rw [← P_eq]
  exact subset_closure ⟨0, by norm_num, by rw [gP, q5PG_eq.1]⟩

theorem perm_three : ∀ σ : Equiv.Perm (Fin 3), (∀ i, σ i ≠ i) → σ ^ 3 = 1 ∧ σ ≠ 1 := by decide

theorem perm_two : ∀ σ : Equiv.Perm (Fin 3), σ 0 = 2 → σ 1 = 1 → σ ^ 2 = 1 ∧ σ ≠ 1 := by decide

theorem B_le_P : (frameOf m).B ≤ normIn (g23T5 m) (frameOf m).B := by
  refine le_inf ?_ (Subgroup.le_normalizer)
  rw [B_eq_cent]
  exact inf_le_left.trans (S_le_T5 m)

theorem B_S3 : SecProp (normIn (g23T5 m) (frameOf m).B) (frameOf m).B
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
  set P := normIn (g23T5 m) (frameOf m).B with hPdef
  let w : Fin 3 → G := fun i => vZ m i.succ
  have hw : ∀ i j : Fin 3, (w j)⁻¹ * w i ∈ (⊥ : Subgroup G) → i = j := by
    intro i j h
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h
    exact (Fin.succ_injective _ (vZ_inj m h)).symm
  have hbot : P ≤ normalizer ((⊥ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun g _ k hk => by
      rw [Subgroup.mem_bot] at hk ⊢
      rw [hk]
      group)
  have hPZ : ∀ x ∈ P, ∀ u ∈ cen (frameOf m).B, x * u * x⁻¹ ∈ cen (frameOf m).B :=
    fun x hx u hu => (mem_normalizer_iff.mp (normIn_le_normIn_cen hx).2 u).mp hu
  have hP : ∀ x ∈ P, ∀ i, ∃ j, (w j)⁻¹ * (x * w i * x⁻¹) ∈ (⊥ : Subgroup G) := by
    intro x hx i
    obtain ⟨k, hk⟩ := eq_of_card4 (card_cen_B m) (vZ m) (vZ_inj m) (vZ_mem m)
      (hPZ x hx _ (vZ_mem m i.succ))
    refine Fin.cases (fun h0 => ?_) (fun j hj => ⟨j, ?_⟩) k hk
    · exfalso
      have h1 : w i = 1 := by
        have : x * w i * x⁻¹ = 1 := h0
        have e : w i = x⁻¹ * (x * w i * x⁻¹) * x := by group
        rw [e, this]
        group
      exact Fin.succ_ne_zero i (vZ_inj m h1)
    · rw [Subgroup.mem_bot, hj]
      exact inv_mul_cancel _
  obtain ⟨φ, hφ⟩ := exists_perm3 w hw hbot hP
  have hφ' : ∀ (x : P) (i : Fin 3), (x : G) * w i * (x : G)⁻¹ = w (φ x i) := fun x i =>
    (inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hφ x i))).symm
  have hfix : ∀ (x : P) (i : Fin 3), (x : G) * w i = w i * x → φ x i = i := by
    intro x i hc
    have e := hφ' x i
    rw [hc, mul_inv_cancel_right] at e
    exact hw _ _ (by rw [Subgroup.mem_bot, ← e, inv_mul_cancel])
  have hτ3 : orderOf (φ ⟨uE m 20, tau_mem_P m⟩) = 3 := by
    have hσ := perm_three (φ ⟨uE m 20, tau_mem_P m⟩) (fun i hi => by
      have e := hφ' ⟨uE m 20, tau_mem_P m⟩ i
      rw [hi] at e
      have hc : uE m 20 * w i = w i * uE m 20 := by
        calc uE m 20 * w i = uE m 20 * w i * (uE m 20)⁻¹ * uE m 20 := by group
          _ = w i * uE m 20 := by rw [e]
      fin_cases i
      · exact nrl m 2 20 9 9 20 (by quickRfl) hc
      · exact nrl m 3 20 10 10 20 (by quickRfl) hc
      · exact nrl m 4 20 23 23 20 (by quickRfl) hc)
    exact orderOf_eq_prime hσ.1 hσ.2
  have ha2 : orderOf (φ ⟨uE m 0, a1_mem_P m⟩) = 2 := by
    have h0 : φ ⟨uE m 0, a1_mem_P m⟩ 0 = 2 := by
      have e := hφ' ⟨uE m 0, a1_mem_P m⟩ 0
      have hc := uE_mul_eq m (a := 0) (b := 9) (c := 23) (d := 0) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl))
      have e2 : uE m 0 * w 0 * (uE m 0)⁻¹ = w 2 := by
        change uE m 0 * uE m 9 * (uE m 0)⁻¹ = uE m 23
        rw [hc, mul_inv_cancel_right]
      rw [e2] at e
      exact hw _ _ (by rw [Subgroup.mem_bot, ← e, inv_mul_cancel])
    have h1 := hfix ⟨uE m 0, a1_mem_P m⟩ 1 (by
      change uE m 0 * uE m 10 = uE m 10 * uE m 0
      exact (rl m 46 0 10 10 0 (by quickRfl)))
    have hσ := perm_two _ h0 h1
    exact orderOf_eq_prime hσ.1 hσ.2
  refine secProp_perm3 (B_le_P m) φ (perm3_surjective φ hτ3 ha2) (fun x hx => ?_) ?_
  · ext i
    refine congrArg Fin.val (hfix x i ?_)
    have hwB : w i ∈ centralizer ((frameOf m).B : Set G) := (vZ_mem m i.succ).2
    exact (mem_centralizer_iff.mp hwB x hx)
  · rw [card_normIn_B, card_B]

theorem reg_of_cosets {τ : G} {V Z : Subgroup G} (hZV : Z ≤ V)
    (hcard : Nat.card V = 4 * Nat.card Z) (hτ : τ ^ 3 = 1) (hτV : τ ∈ normalizer (V : Set G))
    (hτZ : τ ∈ normalizer (Z : Set G)) (w : Fin 4 → G) (hwV : ∀ i, w i ∈ V) (hw0 : w 0 ∈ Z)
    (hw : ∀ i j, (w j)⁻¹ * w i ∈ Z → i = j) (T : Fin 4 → Fin 4) (hT : ∀ i, i ≠ 0 → T i ≠ i)
    (hact : ∀ i, (w (T i))⁻¹ * (τ * w i * τ⁻¹) ∈ Z) : ActsRegularly (zpowers τ) V Z := by
  refine actsRegularly_zpowers hZV hcard hτ hτV hτZ ?_
  intro u hu huZ hfix
  obtain ⟨i, hi⟩ := exists_coset_of_card hZV w hwV hw hcard u hu
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply huZ
    have := Z.mul_mem hw0 hi
    rwa [mul_inv_cancel_left] at this
  have hz0' : τ * ((w i)⁻¹ * u) * τ⁻¹ ∈ Z := (mem_normalizer_iff.mp hτZ _).mp hi
  have key : (w i)⁻¹ * w (T i) = ((w i)⁻¹ * u) * (u⁻¹ * (τ * u * τ⁻¹)) *
      (τ * ((w i)⁻¹ * u) * τ⁻¹)⁻¹ * ((w (T i))⁻¹ * (τ * w i * τ⁻¹))⁻¹ := by
    group
  apply hT i hi0
  apply hw
  rw [key]
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem hi hfix) (Z.inv_mem hz0')) (Z.inv_mem (hact i))

theorem tau_cube : uE m 20 ^ 3 = 1 := by
  have h21 := rl m 13 20 20 21 7 (by quickRfl)
  have h1 := rl m 26 21 20 7 7 (by quickRfl)
  rw [uE_seven, mul_one] at h21 h1
  rw [pow_succ, pow_two, h21, h1]

theorem tau_ne : uE m 20 ≠ 1 := by
  intro h
  apply nrl m 0 20 7 7 7 (by quickRfl)
  rw [h, uE_seven]

theorem tau_order : orderOf (uE m 20) = 3 := orderOf_eq_prime (tau_cube m) (tau_ne m)

theorem sylow3 {V : Subgroup G} {τ : G} (hτ : τ ∈ V) (h3 : orderOf τ = 3) {n : ℕ}
    (hV : Nat.card V = 3 * n) (hn : ¬ 3 ∣ n) : IsSylowIn 3 V (zpowers τ) := by
  have hc : Nat.card (zpowers τ) = 3 := by rw [Nat.card_zpowers, h3]
  refine ⟨(zpowers_le (H := V)).2 hτ, IsPGroup.of_card (n := 1) (by rw [hc]; norm_num), ?_⟩
  have h := relIndex_mul_card (H := zpowers τ) (K := V)
  rw [inf_of_le_left ((zpowers_le (H := V)).2 hτ), hc, hV] at h
  have : (zpowers τ).relIndex V = n := by omega
  rw [this]
  exact hn

theorem q5JG : Q5JG 0 = 1 ∧ Q5JG 1 = 13 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem q5JG_lt : ∀ s < 2, Q5JG s < 34 := by
  intro s hs
  interval_cases s <;> simp [q5JG.1, q5JG.2]

@[expose] noncomputable def gJ (s : ℕ) : G := uE m (Q5JG s)

theorem tabJ : TabOf m.ρ Q5J 16 (closure (gJ m '' {s | s < 2}) : Set G) ∧
    Nat.card (closure (gJ m '' {s | s < 2})) = 16 ∧ ∀ i < 16, ∀ j < 16, Q5J i = Q5J j → i = j :=
  clos_tab m (Gd := fun s => Q5U (Q5JG s)) (g := gJ m) (by norm_num)
    (fun s hs => enc_uE m (q5JG_lt s hs)) q5_ones.2.2.2.2.2.2.2.1 q5_J (by norm_num)
    (by norm_num) (by norm_num)

theorem image2 {f : ℕ → G} {a b : G} (h0 : f 0 = a) (h1 : f 1 = b) :
    f '' {s | s < 2} = {a, b} := by
  ext x
  rw [img_lt]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, hx⟩
    interval_cases s
    · exact Or.inl (hx.symm.trans h0)
    · exact Or.inr (hx.symm.trans h1)
  · rintro (hx | hx)
    · exact ⟨0, by norm_num, h0.trans hx.symm⟩
    · exact ⟨1, by norm_num, h1.trans hx.symm⟩

theorem J_eq : closure (gJ m '' {s | s < 2}) =
    closure {(frameOf m).b₁, (frameOf m).a₁ * (frameOf m).a₂ * (frameOf m).h₀} := by
  have h0 : gJ m 0 = (frameOf m).b₁ := by
    rw [gJ, q5JG.1, uE_gen m (by norm_num)]
    simp [gen5, sGen_one]
  have h1 : gJ m 1 = (frameOf m).a₁ * (frameOf m).a₂ * (frameOf m).h₀ := by
    have h := rl m 5 8 4 13 7 (by quickRfl)
    rw [uE_seven, mul_one, uE_a1a2, uE_h0] at h
    rw [gJ, q5JG.2, ← h]
  rw [image2 h0 h1]

theorem ZB_le_J : cen (frameOf m).B ≤ closure (gJ m '' {s | s < 2}) := by
  rw [cen_B_uE, closure_le]
  intro x hx
  obtain hx | hx := hx
  · rw [hx]
    have e : Q5J 5 = Q5U 9 := Nat.eq_of_beq_eq_true (by quickRfl)
    have he : Enc m.ρ (Q5J 5) (uE m 9) := by
      rw [e]
      exact enc_uE m (by norm_num)
    exact mem_of_tabOf m.inj (tabJ m).1 (by norm_num) he
  · rw [Set.mem_singleton_iff.mp hx]
    have h := rl m 2 1 1 10 7 (by quickRfl)
    rw [uE_seven, mul_one] at h
    have hb : uE m 1 ∈ closure (gJ m '' {s | s < 2}) :=
      subset_closure ⟨0, by norm_num, by rw [gJ, q5JG.1]⟩
    rw [← h]
    exact mul_mem hb hb

theorem P_le_norm_J : closure (gP m '' {s | s < 2}) ≤
    normalizer ((closure (gJ m '' {s | s < 2}) : Subgroup G) : Set G) := by
  have hq := q5_normJ
  simp only [Bool.and_eq_true] at hq
  refine closure_le_normalizer ?_
  rintro p ⟨a, ha, rfl⟩ b ⟨c, hc, rfl⟩
  have ha' : a < 2 := ha
  have hc' : c < 2 := hc
  have h : MULP (Q5U (Q5PG ((2 * a + c) / 2))) (Q5U (Q5JG ((2 * a + c) % 2))) =
      MULP (Q5J (Q5NJW (2 * a + c))) (Q5U (Q5PG ((2 * a + c) / 2))) :=
    eqK_at hq.1 (by norm_num) (2 * a + c) (by omega)
  have e1 : (2 * a + c) / 2 = a := by omega
  have e2 : (2 * a + c) % 2 = c := by omega
  rw [e1, e2] at h
  have hl := ltK_at hq.2 (by norm_num) (2 * a + c) (by omega)
  obtain ⟨x, hx, hxe⟩ := (tabJ m).1.1 _ hl
  have e := mul_eq_of_MULP m.inj (enc_uE m (q5PG_lt a ha')) (enc_uE m (q5JG_lt c hc')) hxe
    (enc_uE m (q5PG_lt a ha')) h
  have e' : gP m a * gJ m c * (gP m a)⁻¹ = x := by
    rw [gP, gJ, e, mul_inv_cancel_right]
  rw [e']
  exact hx

theorem q5ZB_enc : ∀ k : Fin 4, Enc m.ρ (Q5U (Q5ZB k)) (vZ m k) := by
  have h23 := rl m 15 9 10 23 7 (by quickRfl)
  intro k
  fin_cases k
  · have e : Q5ZB 0 = 7 := Nat.eq_of_beq_eq_true (by quickRfl)
    change Enc m.ρ (Q5U (Q5ZB 0)) 1
    rw [e, ← uE_seven m]
    exact enc_uE m (by norm_num)
  · have e : Q5ZB 1 = 9 := Nat.eq_of_beq_eq_true (by quickRfl)
    simp only [vZ]
    rw [e]
    exact enc_uE m (by norm_num)
  · have e : Q5ZB 2 = 10 := Nat.eq_of_beq_eq_true (by quickRfl)
    simp only [vZ]
    rw [e]
    exact enc_uE m (by norm_num)
  · have e : Q5ZB 3 = 23 := Nat.eq_of_beq_eq_true (by quickRfl)
    simp only [vZ]
    rw [e]
    exact enc_uE m (by norm_num)

theorem J_reg : ActsRegularly (zpowers (uE m 20)) (closure (gJ m '' {s | s < 2}))
    (cen (frameOf m).B) := by
  have hq := q5_cosJ
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hW⟩, hT⟩, hZ⟩, hTne⟩, hact1⟩, hact2⟩, hne⟩ := hq
  choose! eJ heJ using (tabJ m).1.1
  have hRl : ∀ q : Fin 4, Q5RJ q < 16 := fun q => ltK_at hR (by norm_num) q q.2
  have hWl : ∀ q : Fin 4, Q5RJW q < 16 := fun q => ltK_at hW (by norm_num) q q.2
  have hTl : ∀ q : Fin 4, Q5RJT q < 4 := fun q => ltK_at hT (by norm_num) q q.2
  have hZl : ∀ q : Fin 4, Q5RJZ q < 4 := fun q => ltK_at hZ (by norm_num) q q.2
  let w : Fin 4 → G := fun q => eJ (Q5RJ q)
  let T : Fin 4 → Fin 4 := fun q => ⟨Q5RJT q, hTl q⟩
  have hτP : uE m 20 ∈ closure (gP m '' {s | s < 2}) := by
    rw [P_eq]
    exact tau_mem_P m
  have hτZ : uE m 20 ∈ normalizer ((cen (frameOf m).B : Subgroup G) : Set G) :=
    (normIn_le_normIn_cen (tau_mem_P m)).2
  have hw0 : w 0 ∈ cen (frameOf m).B := by
    have e : w 0 = 1 := by
      have h0 := (heJ _ (hRl 0)).2
      rw [show Q5RJ ((0 : Fin 4) : ℕ) = 0 from q5_ones.2.2.2.2.2.2.2.2.2.1, q5_ones.2.2.2.2.2.2.2.1]
        at h0
      exact enc_unique m.inj h0 (enc_one m.ρ)
    rw [e]
    exact one_mem _
  have hw : ∀ i j, (w j)⁻¹ * w i ∈ cen (frameOf m).B → i = j := by
    have key : ∀ i j : Fin 4, i.val < j.val → (w j)⁻¹ * w i ∉ cen (frameOf m).B := by
      intro i j hij hmem
      obtain ⟨k, hk⟩ := eq_of_card4 (card_cen_B m) (vZ m) (vZ_inj m) (vZ_mem m) hmem
      have e : w i * 1 = w j * vZ m k := by
        rw [mul_one, ← hk]
        group
      have hp : ∃ p < 6, Q5P4I p = i.val ∧ Q5P4J p = j.val := by
        have := j.2
        have hp4 : ∀ p < 6, Q5P4I p = [0, 0, 0, 1, 1, 2].getD p 0 ∧
            Q5P4J p = [1, 2, 3, 2, 3, 3].getD p 0 := by
          intro p hp
          interval_cases p
          all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
        have hsel : i.val = 0 ∧ j.val = 1 ∨ i.val = 0 ∧ j.val = 2 ∨ i.val = 1 ∧ j.val = 2 ∨
            i.val = 0 ∧ j.val = 3 ∨ i.val = 1 ∧ j.val = 3 ∨ i.val = 2 ∧ j.val = 3 := by omega
        rcases hsel with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
        · exact ⟨0, by norm_num, (hp4 0 (by norm_num)).1, (hp4 0 (by norm_num)).2⟩
        · exact ⟨1, by norm_num, (hp4 1 (by norm_num)).1, (hp4 1 (by norm_num)).2⟩
        · exact ⟨3, by norm_num, (hp4 3 (by norm_num)).1, (hp4 3 (by norm_num)).2⟩
        · exact ⟨2, by norm_num, (hp4 2 (by norm_num)).1, (hp4 2 (by norm_num)).2⟩
        · exact ⟨4, by norm_num, (hp4 4 (by norm_num)).1, (hp4 4 (by norm_num)).2⟩
        · exact ⟨5, by norm_num, (hp4 5 (by norm_num)).1, (hp4 5 (by norm_num)).2⟩
      obtain ⟨p, hp6, hpi, hpj⟩ := hp
      have hn : MULP (Q5J (Q5RJ (Q5P4I ((4 * p + k.val) / 4)))) (Q5U 7) ≠
          MULP (Q5J (Q5RJ (Q5P4J ((4 * p + k.val) / 4)))) (Q5U (Q5ZB ((4 * p + k.val) % 4))) :=
        neK_at hne (by norm_num) (4 * p + k.val) (by omega)
      have e1 : (4 * p + k.val) / 4 = p := by omega
      have e2 : (4 * p + k.val) % 4 = k.val := by omega
      rw [e1, e2, hpi, hpj] at hn
      exact mul_ne_of_MULP (heJ _ (hRl i)).2 (enc_uE m (by norm_num)) (heJ _ (hRl j)).2
        (q5ZB_enc m k) hn (by rw [uE_seven]; exact e)
    intro i j h
    by_contra hne'
    rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne' (Fin.ext e)) with hl | hl
    · exact key i j hl h
    · apply key j i hl
      have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  refine reg_of_cosets (ZB_le_J m) (by rw [(tabJ m).2.1, card_cen_B]) (tau_cube m)
    (P_le_norm_J m hτP) hτZ w (fun q => (heJ _ (hRl q)).1) hw0 hw T ?_ ?_
  · intro i hi0 hTi
    have hi : ∃ q < 3, i.val = q + 1 := ⟨i.val - 1, by omega, by
      have : i.val ≠ 0 := fun e => hi0 (Fin.ext e)
      omega⟩
    obtain ⟨q, hq3, hiq⟩ := hi
    have hn := neqK_at hTne (by norm_num) q hq3
    apply hn
    have := congrArg Fin.val hTi
    simp only [T] at this
    rw [hiq] at this
    exact this
  · intro i
    have h1 : MULP (Q5U 20) (Q5J (Q5RJ i)) = MULP (Q5J (Q5RJW i)) (Q5U 20) :=
      eqK_at hact1 (by norm_num) i i.2
    have h2 : MULP (Q5J (Q5RJW i)) (Q5U 7) = MULP (Q5J (Q5RJ (Q5RJT i))) (Q5U (Q5ZB (Q5RJZ i))) :=
      eqK_at hact2 (by norm_num) i i.2
    obtain ⟨y, -, hy⟩ := (tabJ m).1.1 _ (hWl i)
    have e1 := mul_eq_of_MULP m.inj (enc_uE m (by norm_num)) (heJ _ (hRl i)).2 hy
      (enc_uE m (by norm_num)) h1
    have e2 := mul_eq_of_MULP m.inj hy (enc_uE m (by norm_num)) (heJ _ (hRl (T i))).2
      (q5ZB_enc m ⟨_, hZl i⟩) h2
    rw [uE_seven, mul_one] at e2
    have e3 : uE m 20 * w i * (uE m 20)⁻¹ = y := by
      change uE m 20 * eJ (Q5RJ i) * (uE m 20)⁻¹ = y
      rw [e1, mul_inv_cancel_right]
    rw [e3, e2]
    change (eJ (Q5RJ (Q5RJT i)))⁻¹ * (eJ (Q5RJ (Q5RJT i)) * vZ m ⟨Q5RJZ i, hZl i⟩) ∈ _
    rw [inv_mul_cancel_left]
    exact vZ_mem m _

theorem ZB_reg : ActsRegularly (zpowers (uE m 20)) (cen (frameOf m).B) ⊥ := by
  have hτZ : uE m 20 ∈ normalizer ((cen (frameOf m).B : Subgroup G) : Set G) :=
    (normIn_le_normIn_cen (tau_mem_P m)).2
  refine actsRegularly_zpowers bot_le (by rw [card_cen_B, Subgroup.card_bot]) (tau_cube m) hτZ
    (Subgroup.le_normalizer_iff.mpr (fun g _ k hk => by
      rw [Subgroup.mem_bot] at hk ⊢
      rw [hk]
      group) (mem_top _)) ?_
  intro u hu hu1 hfix
  obtain ⟨k, hk⟩ := eq_of_card4 (card_cen_B m) (vZ m) (vZ_inj m) (vZ_mem m) hu
  rw [Subgroup.mem_bot] at hu1 hfix
  have hc : uE m 20 * u = u * uE m 20 := by
    have e : uE m 20 * u = u * (u⁻¹ * (uE m 20 * u * (uE m 20)⁻¹)) * uE m 20 := by group
    rw [e, hfix, mul_one]
  rw [hk] at hc hu1
  fin_cases k
  · exact hu1 rfl
  · exact nrl m 2 20 9 9 20 (by quickRfl) hc
  · exact nrl m 3 20 10 10 20 (by quickRfl) hc
  · exact nrl m 4 20 23 23 20 (by quickRfl) hc

theorem B_sylow : ∀ T : Subgroup G, IsSylowIn 3 (normIn (g23T5 m) (frameOf m).B) T →
    ActsRegularly T (cen (frameOf m).B) ⊥ ∧
      ActsRegularly T (closure {(frameOf m).b₁, (frameOf m).a₁ * (frameOf m).a₂ * (frameOf m).h₀})
        (cen (frameOf m).B) := by
  have h0 : IsSylowIn 3 (normIn (g23T5 m) (frameOf m).B) (zpowers (uE m 20)) :=
    sylow3 (tau_mem_P m) (tau_order m) (n := 64) (by rw [card_normIn_B]) (by norm_num)
  rw [← J_eq]
  refine forall_isSylowIn_of_one h0 ⟨ZB_reg m, J_reg m⟩ (fun g hg h => ⟨?_, ?_⟩)
  · exact actsRegularly_conj (normIn_le_normIn_cen hg).2
      (Subgroup.le_normalizer_iff.mpr (fun g _ k hk => by
        rw [Subgroup.mem_bot] at hk ⊢
        rw [hk]
        group) (mem_top _)) h.1
  · have hgP : g ∈ closure (gP m '' {s | s < 2}) := by
      rw [P_eq]
      exact hg
    exact actsRegularly_conj (P_le_norm_J m hgP) (normIn_le_normIn_cen hg).2 h.2

@[expose] noncomputable def pF (c : ℕ) : G := pwG (fun s => uE m (s + 8)) 3 c

theorem pF_mul (c d : ℕ) : pF m c * pF m d = pF m (c ^^^ d) := pwG_mul (F_gens m).2 (F_gens m).1 c d

theorem pF_zero : pF m 0 = 1 := by
  simp [pF, pwG]
  rfl

theorem pF_inv (c : ℕ) : (pF m c)⁻¹ = pF m c := by
  have h := pF_mul m c c
  rw [Nat.xor_self, pF_zero] at h
  exact inv_eq_of_mul_eq_one_right h

theorem pF_z : pF m 4 = (frameOf m).z :=
  (pwG_two_pow (g := fun s => uE m (s + 8)) (r := 3) (j := 2) (by norm_num)).trans (uE_z m)

theorem pF_mem {c : ℕ} (hc : c < 8) : pF m c ∈ (frameOf m).F :=
  mem_of_tabOf m.inj (tabF' m) hc (enc_F m hc)

theorem F_elem {x : G} (hx : x ∈ (frameOf m).F) : ∃ c < 8, x = pF m c := by
  obtain ⟨c, hc, he⟩ := (tabF' m).2 x hx
  exact ⟨c, hc, enc_unique m.inj he (enc_F m hc)⟩

theorem pF_inj {c d : ℕ} (hc : c < 8) (hd : d < 8) (h : pF m c = pF m d) : c = d :=
  F_inj m c hc d hd h

theorem conjP {s : ℕ} (hs : s < 9) (hMG : Q5MG s < 34) {j : ℕ} (hj : j < 3) :
    uE m (Q5MG s) * pF m (2 ^ j) * (uE m (Q5MG s))⁻¹ = pF m ((Q5M s >>> (3 * j)) &&& 7) := by
  have h := actK_at q5_act (by norm_num) s hs j hj
  have hcol : (Q5M s >>> (3 * j)) &&& 7 < 8 := Nat.lt_succ_of_le Nat.and_le_right
  have h' := mul_eq_of_MULP m.inj (enc_uE m hMG) (enc_F m (c := 2 ^ j)
    (by interval_cases j <;> norm_num)) (enc_F m hcol) (enc_uE m hMG) h
  rw [pF, pF, h', mul_inv_cancel_right]

@[expose] def cw (i : Fin 3) : ℕ := ![1, 2, 3] i

theorem pF_one_two : pF m 3 = pF m 1 * pF m 2 := by
  rw [pF_mul]
  rfl

theorem conj3 {x : G} {a b : ℕ} (ha : x * pF m 1 * x⁻¹ = pF m a) (hb : x * pF m 2 * x⁻¹ = pF m b) :
    ∀ i : Fin 3, x * pF m (cw i) * x⁻¹ = pF m (![a, b, a ^^^ b] i) := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · change x * pF m 3 * x⁻¹ = pF m (a ^^^ b)
    rw [← pF_mul, ← ha, ← hb, pF_one_two]
    group

theorem z_sq : (frameOf m).z * (frameOf m).z = 1 := by
  rw [← uE_z]
  exact (F_gens m).1 2 (by norm_num)

theorem z_ne : (frameOf m).z ≠ 1 := by
  intro h
  rw [← pF_z, ← pF_zero m] at h
  exact absurd (pF_inj m (by norm_num) (by norm_num) h) (by norm_num)

theorem Z_elem {x : G} (hx : x ∈ (frameOf m).Z) : x = 1 ∨ x = (frameOf m).z := by
  have ho : orderOf (frameOf m).z = 2 := orderOf_eq_prime (by rw [pow_two]; exact z_sq m) (z_ne m)
  have hc : Nat.card (frameOf m).Z = 2 := by rw [SFrame.Z, Nat.card_zpowers, ho]
  by_contra h
  simp only [not_or] at h
  let f : Option Bool → (frameOf m).Z := fun o => match o with
    | none => ⟨x, hx⟩
    | some false => ⟨1, one_mem _⟩
    | some true => ⟨(frameOf m).z, mem_zpowers _⟩
  have hf : Function.Injective f := by
    rintro (_ | _ | _) (_ | _ | _) hij <;> have e := congrArg Subtype.val hij <;>
      simp only [f] at e
    all_goals first | rfl | exact absurd e h.1 | exact absurd e h.2 | exact absurd e.symm h.1 |
      exact absurd e.symm h.2 | exact absurd e (z_ne m).symm | exact absurd e (z_ne m)
  have := Nat.card_le_card_of_injective f hf
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_bool] at this
  omega

theorem pF_mem_Z_iff {c : ℕ} (hc : c < 8) : pF m c ∈ (frameOf m).Z ↔ c = 0 ∨ c = 4 := by
  constructor
  · intro h
    rcases Z_elem m h with h | h
    · rw [← pF_zero m] at h
      exact Or.inl (pF_inj m hc (by norm_num) h)
    · rw [← pF_z m] at h
      exact Or.inr (pF_inj m hc (by norm_num) h)
  · rintro (rfl | rfl)
    · rw [pF_zero]
      exact one_mem _
    · rw [pF_z]
      exact mem_zpowers _

theorem cw_lt (i : Fin 3) : cw i < 8 := by fin_cases i <;> decide

theorem cw_inv_mul (i j : Fin 3) : (pF m (cw j))⁻¹ * pF m (cw i) = pF m (cw j ^^^ cw i) := by
  rw [pF_inv, pF_mul]

theorem xor_lt {a b : ℕ} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 := by
  interval_cases a <;> interval_cases b <;> decide

theorem point_of {x : G} (i : Fin 3) {c : ℕ} (hc : c < 8) (hxc : x * pF m (cw i) * x⁻¹ = pF m c)
    (j : Fin 3) (hj : (pF m (cw j))⁻¹ * (x * pF m (cw i) * x⁻¹) ∈ (frameOf m).Z) :
    cw j ^^^ c = 0 ∨ cw j ^^^ c = 4 := by
  rw [hxc, pF_inv, pF_mul] at hj
  exact (pF_mem_Z_iff m (xor_lt (cw_lt j) hc)).mp hj

theorem cw_unique : ∀ c < 8, ∀ j j' : Fin 3, (cw j ^^^ c = 0 ∨ cw j ^^^ c = 4) →
    (cw j' ^^^ c = 0 ∨ cw j' ^^^ c = 4) → j = j' := by decide

theorem cw_exists : ∀ c < 8, c ≠ 0 → c ≠ 4 → ∃ j : Fin 3, cw j ^^^ c = 0 ∨ cw j ^^^ c = 4 := by
  decide

theorem q5CG : Q5CG 0 = 5 ∧ Q5CG 1 = 17 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem q5CG_lt : ∀ s < 2, Q5CG s < 34 := by
  intro s hs
  interval_cases s <;> simp [q5CG.1, q5CG.2]

@[expose] noncomputable def gC (s : ℕ) : G := uE m (Q5CG s)

theorem tabC : TabOf m.ρ Q5C 192 (closure (gC m '' {s | s < 2}) : Set G) ∧
    Nat.card (closure (gC m '' {s | s < 2})) = 192 ∧ ∀ i < 192, ∀ j < 192, Q5C i = Q5C j → i = j :=
  clos_tab m (Gd := fun s => Q5U (Q5CG s)) (g := gC m) (by norm_num)
    (fun s hs => enc_uE m (q5CG_lt s hs)) q5_ones.2.2.2.2.2.2.1 q5_C (by norm_num) (by norm_num)
    (by norm_num)

theorem C_le : closure (gC m '' {s | s < 2}) ≤ centEl (g23T5 m) (frameOf m).z := by
  rw [closure_le]
  rintro x ⟨s, hs, rfl⟩
  refine ⟨uE_mem m _, mem_centralizer_singleton_iff.mpr ?_⟩
  have hs' : s < 2 := hs
  rw [← uE_z]
  interval_cases s
  · rw [gC, q5CG.1]
    exact rl m 44 5 10 10 5 (by quickRfl)
  · rw [gC, q5CG.2]
    exact rl m 45 17 10 10 17 (by quickRfl)

theorem C_eq : closure (gC m '' {s | s < 2}) = centEl (g23T5 m) (frameOf m).z := by
  refine Subgroup.eq_of_le_of_card_ge (C_le m) ?_
  rw [(tabC m).2.1]
  have hq := q5_conjZ
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨he, hl⟩, hn⟩ := hq
  have hlt : ∀ i < 7, Q5CZ i < 34 := by
    intro i hi
    interval_cases i <;> decide
  have hconj : ∀ i : Fin 7, uE m (Q5CZ i) * (frameOf m).z * (uE m (Q5CZ i))⁻¹ = pF m (Q5CZW i) := by
    intro i
    have h : MULP (Q5U (Q5CZ i)) (Q5U 10) = MULP (Q5F (Q5CZW i)) (Q5U (Q5CZ i)) :=
      eqK_at he (by norm_num) i i.2
    have hw := ltK_at hl (by norm_num) i i.2
    have e := mul_eq_of_MULP m.inj (enc_uE m (hlt i i.2)) (enc_uE m (by norm_num)) (enc_F m hw)
      (enc_uE m (hlt i i.2)) h
    rw [← uE_z, e, mul_inv_cancel_right, pF]
  have h7 := card_mul_card_centEl_le (T := g23T5 m) (z := (frameOf m).z)
    (fun i : Fin 7 => uE m (Q5CZ i)) (fun i => uE_mem m _) (fun i j h => by
      rw [hconj, hconj] at h
      have hij := pF_inj m (ltK_at hl (by norm_num) i i.2) (ltK_at hl (by norm_num) j j.2) h
      by_contra hne
      rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne (Fin.ext e)) with hlt' | hlt'
      · obtain ⟨hpi, hpj⟩ := q5P7 j.val j.2 i.val hlt'
        have := neqK_at hn (by norm_num) (j.val * (j.val - 1) / 2 + i.val)
          (by have := j.2; interval_cases (j : ℕ) <;> omega)
        simp only [hpi, hpj] at this
        exact this hij
      · obtain ⟨hpi, hpj⟩ := q5P7 i.val i.2 j.val hlt'
        have := neqK_at hn (by norm_num) (i.val * (i.val - 1) / 2 + j.val)
          (by have := i.2; interval_cases (i : ℕ) <;> omega)
        simp only [hpi, hpj] at this
        exact this hij.symm)
  rw [card_T5] at h7
  omega

theorem card_C : Nat.card (centEl (g23T5 m) (frameOf m).z) = 192 := by
  rw [← C_eq]
  exact (tabC m).2.1

theorem A_eq : closure (uE m '' {s | s < 4}) = (frameOf m).A := by
  have e : uE m '' {s | s < 4} = {(frameOf m).a₁, (frameOf m).b₁, (frameOf m).a₂, (frameOf m).b₂} := by
    ext x
    rw [img_lt]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [uE_gen m (by omega)]
      interval_cases s <;> simp [gen5, sGen_zero, sGen_one, sGen_two, sGen_three]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_zero]⟩
      · exact ⟨1, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_one]⟩
      · exact ⟨2, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_two]⟩
      · exact ⟨3, by norm_num, by rw [uE_gen m (by norm_num)]; simp [gen5, sGen_three]⟩
  rw [e]
  rfl

theorem tabA : TabOf m.ρ Q5A 32 (closure (uE m '' {s | s < 4}) : Set G) ∧
    Nat.card (closure (uE m '' {s | s < 4})) = 32 ∧ ∀ i < 32, ∀ j < 32, Q5A i = Q5A j → i = j :=
  clos_tab m (g := uE m) (by norm_num) (fun s hs => enc_uE m (by omega))
    q5_ones.2.2.2.1 q5_A (by norm_num) (by norm_num) (by norm_num)

theorem card_A : Nat.card (frameOf m).A = 32 := by
  rw [← A_eq]
  exact (tabA m).2.1

theorem A_le_C : (frameOf m).A ≤ centEl (g23T5 m) (frameOf m).z := by
  rw [← A_eq, closure_le]
  rintro x ⟨s, hs, rfl⟩
  refine ⟨uE_mem m _, mem_centralizer_singleton_iff.mpr ?_⟩
  have hs' : s < 4 := hs
  rw [← uE_z]
  interval_cases s
  · exact rl m 46 0 10 10 0 (by quickRfl)
  · exact (rl m 42 10 1 1 10 (by quickRfl)).symm
  · exact rl m 47 2 10 10 2 (by quickRfl)
  · exact (rl m 43 10 3 3 10 (by quickRfl)).symm

theorem q5MG_vals : Q5MG 2 = 0 ∧ Q5MG 4 = 5 ∧ Q5MG 5 = 17 ∧ Q5MG 6 = 1 ∧ Q5MG 7 = 2 ∧
    Q5MG 8 = 3 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem conj01 {s : ℕ} (hs : s < 9) (hMG : Q5MG s < 34) {a b : ℕ}
    (ha : (Q5M s >>> (3 * 0)) &&& 7 = a) (hb : (Q5M s >>> (3 * 1)) &&& 7 = b) :
    uE m (Q5MG s) * pF m 1 * (uE m (Q5MG s))⁻¹ = pF m a ∧
      uE m (Q5MG s) * pF m 2 * (uE m (Q5MG s))⁻¹ = pF m b := by
  have h0 := conjP m hs hMG (j := 0) (by norm_num)
  have h1 := conjP m hs hMG (j := 1) (by norm_num)
  rw [ha] at h0
  rw [hb] at h1
  exact ⟨h0, h1⟩

theorem F_S3_aux : SecProp (centEl (g23T5 m) (frameOf m).z) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
      centEl (g23T5 m) (frameOf m).z ≤ normalizer ((frameOf m).A : Set G) := by
  set C := centEl (g23T5 m) (frameOf m).z with hCdef
  let w : Fin 3 → G := fun i => pF m (cw i)
  have hw : ∀ i j : Fin 3, (w j)⁻¹ * w i ∈ (frameOf m).Z → i = j := by
    intro i j h
    have h' := (pF_mem_Z_iff m (xor_lt (cw_lt j) (cw_lt i))).mp (by rw [← cw_inv_mul]; exact h)
    have hi : cw i ^^^ cw i = 0 := Nat.xor_self _
    exact (cw_unique (cw i) (cw_lt i) j i h' (Or.inl hi)).symm
  have hCF : ∀ x ∈ C, x ∈ normalizer ((frameOf m).F : Set G) := fun x hx => T5_le_norm_F m hx.1
  have hCZ : C ≤ normalizer ((frameOf m).Z : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    have hgcen : g ∈ Subgroup.centralizer ({(frameOf m).z} : Set G) := hg.2
    simpa only [SFrame.Z, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hgcen
  have hP : ∀ x ∈ C, ∀ i, ∃ j, (w j)⁻¹ * (x * w i * x⁻¹) ∈ (frameOf m).Z := by
    intro x hx i
    have hy : x * w i * x⁻¹ ∈ (frameOf m).F := (mem_normalizer_iff.mp (hCF x hx) _).mp (pF_mem m (cw_lt i))
    obtain ⟨c, hc, hyc⟩ := F_elem m hy
    have hc0 : c ≠ 0 ∧ c ≠ 4 := by
      constructor <;> rintro rfl
      · rw [pF_zero] at hyc
        have : w i = 1 := by
          have e : w i = x⁻¹ * (x * w i * x⁻¹) * x := by group
          rw [e, hyc]
          group
        have := pF_inj m (cw_lt i) (by norm_num) (this.trans (pF_zero m).symm)
        fin_cases i <;> simp [cw] at this
      · rw [pF_z] at hyc
        have hz : w i ∈ (frameOf m).Z := by
          have e : w i = x⁻¹ * (x * w i * x⁻¹) * x := by group
          rw [e, hyc]
          have hxi : x⁻¹ ∈ normalizer ((frameOf m).Z : Set G) := inv_mem (hCZ hx)
          have := (mem_normalizer_iff.mp hxi (frameOf m).z).mp (mem_zpowers _)
          simpa using this
        have := (pF_mem_Z_iff m (cw_lt i)).mp hz
        fin_cases i <;> simp [cw] at this
    obtain ⟨j, hj⟩ := cw_exists c hc hc0.1 hc0.2
    refine ⟨j, ?_⟩
    rw [hyc]
    change (pF m (cw j))⁻¹ * pF m c ∈ _
    rw [pF_inv, pF_mul]
    exact (pF_mem_Z_iff m (xor_lt (cw_lt j) hc)).mpr hj
  obtain ⟨φ, hφ⟩ := exists_perm3 w hw hCZ hP
  have hval : ∀ (x : C) (i : Fin 3) {c : ℕ}, c < 8 → (x : G) * pF m (cw i) * (x : G)⁻¹ = pF m c →
      ∀ j : Fin 3, (cw j ^^^ c = 0 ∨ cw j ^^^ c = 4) → φ x i = j := by
    intro x i c hc hxc j hj
    exact cw_unique c hc _ _ (point_of m i hc hxc _ (hφ x i)) hj
  have hgC : ∀ s : ℕ, (s = 4 ∨ s = 5) → uE m (Q5MG s) ∈ C := by
    rintro s (rfl | rfl)
    · rw [hCdef, ← C_eq, q5MG_vals.2.1]
      exact subset_closure ⟨0, by norm_num, by rw [gC, q5CG.1]⟩
    · rw [hCdef, ← C_eq, q5MG_vals.2.2.1]
      exact subset_closure ⟨1, by norm_num, by rw [gC, q5CG.2]⟩
  have hk3 : orderOf (φ ⟨uE m (Q5MG 4), hgC 4 (Or.inl rfl)⟩) = 3 := by
    obtain ⟨ha, hb⟩ := conj01 m (s := 4) (by norm_num) (by rw [q5MG_vals.2.1]; norm_num)
      (a := 3) (b := 1) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    have h3 := conj3 m ha hb
    have hσ := perm_three (φ ⟨uE m (Q5MG 4), hgC 4 (Or.inl rfl)⟩) (fun i hi => by
      have hz := hφ ⟨_, hgC 4 (Or.inl rfl)⟩ i
      rw [hi] at hz
      fin_cases i
      · exact absurd (point_of m 0 (c := 3) (by norm_num) (h3 0) 0 hz) (by decide)
      · exact absurd (point_of m 1 (c := 1) (by norm_num) (h3 1) 1 hz) (by decide)
      · exact absurd (point_of m 2 (c := 2) (by norm_num) (h3 2) 2 hz) (by decide))
    exact orderOf_eq_prime hσ.1 hσ.2
  have hg2 : orderOf (φ ⟨uE m (Q5MG 5), hgC 5 (Or.inr rfl)⟩) = 2 := by
    obtain ⟨ha, hb⟩ := conj01 m (s := 5) (by norm_num) (by rw [q5MG_vals.2.2.1]; norm_num)
      (a := 3) (b := 6) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    have h3 := conj3 m ha hb
    have h0 := hval ⟨_, hgC 5 (Or.inr rfl)⟩ 0 (by norm_num) (h3 0) 2 (by decide)
    have h1 := hval ⟨_, hgC 5 (Or.inr rfl)⟩ 1 (by norm_num) (h3 1) 1 (by decide)
    have hσ := perm_two _ h0 h1
    exact orderOf_eq_prime hσ.1 hσ.2
  have hgen : ∀ s, (s = 2 ∨ s = 6 ∨ s = 7 ∨ s = 8) → ∀ (h : uE m (Q5MG s) ∈ C), φ ⟨_, h⟩ = 1 := by
    intro s hs h
    have hMG : Q5MG s < 34 := by
      rcases hs with rfl | rfl | rfl | rfl <;> simp [q5MG_vals]
    have hs9 : s < 9 := by omega
    have key : ∀ a b : ℕ, (Q5M s >>> (3 * 0)) &&& 7 = a → (Q5M s >>> (3 * 1)) &&& 7 = b →
        ∀ i : Fin 3, cw i ^^^ (![a, b, a ^^^ b] i) = 0 ∨ cw i ^^^ (![a, b, a ^^^ b] i) = 4 →
          ![a, b, a ^^^ b] i < 8 → φ ⟨_, h⟩ i = i := by
      intro a b ha hb i hi hlt
      obtain ⟨h0, h1⟩ := conj01 m hs9 hMG ha hb
      exact hval ⟨_, h⟩ i hlt (conj3 m h0 h1 i) i hi
    ext i
    simp only [Equiv.Perm.coe_one, id_eq]
    rcases hs with rfl | rfl | rfl | rfl
    · exact congrArg Fin.val (key 1 6 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
    · exact congrArg Fin.val (key 5 2 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
    · exact congrArg Fin.val (key 1 6 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
    · exact congrArg Fin.val (key 5 2 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
  have hAker : (frameOf m).A ≤ φ.ker.map C.subtype := by
    rw [← A_eq, closure_le]
    rintro x ⟨s, hs, rfl⟩
    have hs' : s < 4 := hs
    have hxC : uE m s ∈ C := A_le_C m (by rw [← A_eq]; exact subset_closure ⟨s, hs, rfl⟩)
    refine ⟨⟨uE m s, hxC⟩, ?_, rfl⟩
    obtain ⟨v2, -, -, v6, v7, v8⟩ := q5MG_vals
    interval_cases s
    · have := hgen 2 (Or.inl rfl) (by rw [v2]; exact hxC)
      simp only [v2] at this
      exact this
    · have := hgen 6 (Or.inr (Or.inl rfl)) (by rw [v6]; exact hxC)
      simp only [v6] at this
      exact this
    · have := hgen 7 (Or.inr (Or.inr (Or.inl rfl))) (by rw [v7]; exact hxC)
      simp only [v7] at this
      exact this
    · have := hgen 8 (Or.inr (Or.inr (Or.inr rfl))) (by rw [v8]; exact hxC)
      simp only [v8] at this
      exact this
  have hsurj := perm3_surjective φ hk3 hg2
  refine ⟨secProp_perm3 (A_le_C m) φ hsurj (fun x hx => ?_) ?_, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hAker hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rw [card_C, card_A]
  ·
    have hk : Nat.card (φ.ker.map C.subtype) = 32 := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective]
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv,
        Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, card_C] at h1
      rw [show Nat.factorial 3 = 6 from rfl] at h1
      omega
    have hA : (frameOf m).A = φ.ker.map C.subtype :=
      Subgroup.eq_of_le_of_card_ge hAker (by rw [hk, card_A])
    rw [hA, Subgroup.le_normalizer_iff]
    rintro g hg _ ⟨y, hy, rfl⟩
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (MonoidHom.normal_ker φ).conj_mem y hy ⟨g, hg⟩

theorem F_S3 : SecProp (centEl (g23T5 m) (frameOf m).z) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := (F_S3_aux m).1

theorem C_norm_A : centEl (g23T5 m) (frameOf m).z ≤ normalizer ((frameOf m).A : Set G) :=
  (F_S3_aux m).2

theorem C_le_norm_Z : centEl (g23T5 m) (frameOf m).z ≤ normalizer ((frameOf m).Z : Set G) := by
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ ?_
  have hgcen : g ∈ Subgroup.centralizer ({(frameOf m).z} : Set G) := hg.2
  simpa only [SFrame.Z, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hgcen

theorem k3_cube : uE m 5 ^ 3 = 1 := by
  have h22 := rl m 14 5 5 22 7 (by quickRfl)
  have h1 := rl m 27 22 5 7 7 (by quickRfl)
  rw [uE_seven, mul_one] at h22 h1
  rw [pow_succ, pow_two, h22, h1]

theorem k3_order : orderOf (uE m 5) = 3 := by
  refine orderOf_eq_prime (k3_cube m) (fun h => ?_)
  apply nrl m 1 5 7 7 7 (by quickRfl)
  rw [h, uE_seven]

theorem k3_mem_C : uE m 5 ∈ centEl (g23T5 m) (frameOf m).z := by
  rw [← C_eq]
  exact subset_closure ⟨0, by norm_num, by rw [gC, q5CG.1]⟩

theorem k3_norm_F : uE m 5 ∈ normalizer ((frameOf m).F : Set G) := by
  have := norm_F m (s := 4) (by norm_num)
  rwa [q5MG_vals.2.1] at this

theorem card_Z : Nat.card (frameOf m).Z = 2 := by
  have ho : orderOf (frameOf m).z = 2 := orderOf_eq_prime (by rw [pow_two]; exact z_sq m) (z_ne m)
  rw [SFrame.Z, Nat.card_zpowers, ho]

theorem Z_le_F : (frameOf m).Z ≤ (frameOf m).F := by
  rw [SFrame.Z, zpowers_le, ← pF_z]
  exact pF_mem m (by norm_num)

theorem F_reg : ActsRegularly (zpowers (uE m 5)) (frameOf m).F (frameOf m).Z := by
  obtain ⟨ha, hb⟩ := conj01 m (s := 4) (by norm_num) (by rw [q5MG_vals.2.1]; norm_num)
    (a := 3) (b := 1) (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
  rw [q5MG_vals.2.1] at ha hb
  have h3 := conj3 m ha hb 2
  have hT : ∀ i : Fin 4, i ≠ 0 → (![0, 3, 1, 2] : Fin 4 → Fin 4) i ≠ i := by decide
  have hxor : ∀ i j : Fin 4, (j.val ^^^ i.val = 0 ∨ j.val ^^^ i.val = 4) → i = j := by decide
  refine reg_of_cosets (Z_le_F m) (by rw [card_F, card_Z]) (k3_cube m) (k3_norm_F m)
    (C_le_norm_Z m (k3_mem_C m)) (fun i => pF m i.val) (fun i => pF_mem m (by omega))
    (by change pF m 0 ∈ _; rw [pF_zero]; exact one_mem _) (fun i j h => ?_) ![0, 3, 1, 2] hT
    (fun i => ?_)
  · rw [pF_inv, pF_mul] at h
    exact hxor i j ((pF_mem_Z_iff m (xor_lt (by omega) (by omega))).mp h)
  · fin_cases i
    · change (pF m 0)⁻¹ * (uE m 5 * pF m 0 * (uE m 5)⁻¹) ∈ _
      rw [pF_zero]
      simp only [mul_one, mul_inv_cancel, inv_one]
      exact one_mem _
    · change (pF m 3)⁻¹ * (uE m 5 * pF m 1 * (uE m 5)⁻¹) ∈ _
      rw [ha, inv_mul_cancel]
      exact one_mem _
    · change (pF m 1)⁻¹ * (uE m 5 * pF m 2 * (uE m 5)⁻¹) ∈ _
      rw [hb, inv_mul_cancel]
      exact one_mem _
    · change (pF m 2)⁻¹ * (uE m 5 * pF m (cw 2) * (uE m 5)⁻¹) ∈ _
      rw [h3]
      change (pF m 2)⁻¹ * pF m 2 ∈ _
      rw [inv_mul_cancel]
      exact one_mem _

theorem F_le_A : (frameOf m).F ≤ (frameOf m).A := by
  rw [← F_eq, ← A_eq, closure_le]
  rintro x ⟨s, hs, rfl⟩
  have hs' : s < 3 := hs
  have hm : ∀ t < 4, uE m t ∈ closure (uE m '' {s | s < 4}) := fun t ht => subset_closure ⟨t, ht, rfl⟩
  interval_cases s
  · have h := rl m 0 0 2 8 7 (by quickRfl)
    rw [uE_seven, mul_one] at h
    change uE m 8 ∈ _
    rw [← h]
    exact mul_mem (hm 0 (by norm_num)) (hm 2 (by norm_num))
  · have h := rl m 1 1 3 9 7 (by quickRfl)
    rw [uE_seven, mul_one] at h
    change uE m 9 ∈ _
    rw [← h]
    exact mul_mem (hm 1 (by norm_num)) (hm 3 (by norm_num))
  · have h := rl m 2 1 1 10 7 (by quickRfl)
    rw [uE_seven, mul_one] at h
    change uE m 10 ∈ _
    rw [← h]
    exact mul_mem (hm 1 (by norm_num)) (hm 1 (by norm_num))

theorem tabA' : TabOf m.ρ Q5A 32 ((frameOf m).A : Set G) := by
  rw [← A_eq]
  exact (tabA m).1

theorem A_reg : ActsRegularly (zpowers (uE m 5)) (frameOf m).A (frameOf m).F := by
  have hq := q5_cosA
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hW⟩, hT⟩, hZ⟩, hTne⟩, hact1⟩, hact2⟩, hne⟩ := hq
  choose! eA heA using (tabA' m).1
  have hRl : ∀ q : Fin 4, Q5RAR q < 32 := fun q => ltK_at hR (by norm_num) q q.2
  have hWl : ∀ q : Fin 4, Q5RAW q < 32 := fun q => ltK_at hW (by norm_num) q q.2
  have hTl : ∀ q : Fin 4, Q5RAT q < 4 := fun q => ltK_at hT (by norm_num) q q.2
  have hZl : ∀ q : Fin 4, Q5RAF q < 8 := fun q => ltK_at hZ (by norm_num) q q.2
  let w : Fin 4 → G := fun q => eA (Q5RAR q)
  let T : Fin 4 → Fin 4 := fun q => ⟨Q5RAT q, hTl q⟩
  have hw0 : w 0 ∈ (frameOf m).F := by
    have e : w 0 = 1 := by
      have h0 := (heA _ (hRl 0)).2
      rw [show Q5RAR ((0 : Fin 4) : ℕ) = 0 from q5_ones.2.2.2.2.2.2.2.2.2.2, q5_ones.2.2.2.1] at h0
      exact enc_unique m.inj h0 (enc_one m.ρ)
    rw [e]
    exact one_mem _
  have hw : ∀ i j, (w j)⁻¹ * w i ∈ (frameOf m).F → i = j := by
    have key : ∀ i j : Fin 4, i.val < j.val → (w j)⁻¹ * w i ∉ (frameOf m).F := by
      intro i j hij hmem
      obtain ⟨k, hk8, hk⟩ := F_elem m hmem
      have e : w i * 1 = w j * pF m k := by
        rw [mul_one, ← hk]
        group
      have hp4 : ∀ p < 6, Q5P4I p = [0, 0, 0, 1, 1, 2].getD p 0 ∧
          Q5P4J p = [1, 2, 3, 2, 3, 3].getD p 0 := by
        intro p hp
        interval_cases p
        all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
      have hp : ∃ p < 6, Q5P4I p = i.val ∧ Q5P4J p = j.val := by
        have hsel : i.val = 0 ∧ j.val = 1 ∨ i.val = 0 ∧ j.val = 2 ∨ i.val = 1 ∧ j.val = 2 ∨
            i.val = 0 ∧ j.val = 3 ∨ i.val = 1 ∧ j.val = 3 ∨ i.val = 2 ∧ j.val = 3 := by omega
        rcases hsel with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
        · exact ⟨0, by norm_num, (hp4 0 (by norm_num)).1, (hp4 0 (by norm_num)).2⟩
        · exact ⟨1, by norm_num, (hp4 1 (by norm_num)).1, (hp4 1 (by norm_num)).2⟩
        · exact ⟨3, by norm_num, (hp4 3 (by norm_num)).1, (hp4 3 (by norm_num)).2⟩
        · exact ⟨2, by norm_num, (hp4 2 (by norm_num)).1, (hp4 2 (by norm_num)).2⟩
        · exact ⟨4, by norm_num, (hp4 4 (by norm_num)).1, (hp4 4 (by norm_num)).2⟩
        · exact ⟨5, by norm_num, (hp4 5 (by norm_num)).1, (hp4 5 (by norm_num)).2⟩
      obtain ⟨p, hp6, hpi, hpj⟩ := hp
      have hn : MULP (Q5A (Q5RAR (Q5P4I ((8 * p + k) / 8)))) (Q5U 7) ≠
          MULP (Q5A (Q5RAR (Q5P4J ((8 * p + k) / 8)))) (Q5F ((8 * p + k) % 8)) :=
        neK_at hne (by norm_num) (8 * p + k) (by omega)
      have e1 : (8 * p + k) / 8 = p := by omega
      have e2 : (8 * p + k) % 8 = k := by omega
      rw [e1, e2, hpi, hpj] at hn
      exact mul_ne_of_MULP (heA _ (hRl i)).2 (enc_uE m (by norm_num)) (heA _ (hRl j)).2
        (enc_F m hk8) hn (by rw [uE_seven]; exact e)
    intro i j h
    by_contra hne'
    rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne' (Fin.ext e)) with hl | hl
    · exact key i j hl h
    · apply key j i hl
      have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  refine reg_of_cosets (F_le_A m) (by rw [card_A, card_F]) (k3_cube m)
    (C_norm_A m (k3_mem_C m)) (k3_norm_F m) w (fun q => (heA _ (hRl q)).1) hw0 hw T ?_ ?_
  · intro i hi0 hTi
    obtain ⟨q, hq3, hiq⟩ : ∃ q < 3, i.val = q + 1 := ⟨i.val - 1, by omega, by
      have : i.val ≠ 0 := fun e => hi0 (Fin.ext e)
      omega⟩
    have hn := neqK_at hTne (by norm_num) q hq3
    apply hn
    have := congrArg Fin.val hTi
    simp only [T] at this
    rw [hiq] at this
    exact this
  · intro i
    have h1 : MULP (Q5U 5) (Q5A (Q5RAR i)) = MULP (Q5A (Q5RAW i)) (Q5U 5) :=
      eqK_at hact1 (by norm_num) i i.2
    have h2 : MULP (Q5A (Q5RAW i)) (Q5U 7) = MULP (Q5A (Q5RAR (Q5RAT i))) (Q5F (Q5RAF i)) :=
      eqK_at hact2 (by norm_num) i i.2
    obtain ⟨y, -, hy⟩ := (tabA' m).1 _ (hWl i)
    have e1 := mul_eq_of_MULP m.inj (enc_uE m (by norm_num)) (heA _ (hRl i)).2 hy
      (enc_uE m (by norm_num)) h1
    have e2 := mul_eq_of_MULP m.inj hy (enc_uE m (by norm_num)) (heA _ (hRl (T i))).2
      (enc_F m (hZl i)) h2
    rw [uE_seven, mul_one] at e2
    have e3 : uE m 5 * w i * (uE m 5)⁻¹ = y := by
      change uE m 5 * eA (Q5RAR i) * (uE m 5)⁻¹ = y
      rw [e1, mul_inv_cancel_right]
    rw [e3, e2]
    change (eA (Q5RAR (Q5RAT i)))⁻¹ * (eA (Q5RAR (Q5RAT i)) * pwG _ 3 (Q5RAF i)) ∈ _
    rw [inv_mul_cancel_left]
    exact pF_mem m (hZl i)

theorem F_sylow : ∀ T : Subgroup G, IsSylowIn 3 (centEl (g23T5 m) (frameOf m).z) T →
    ActsRegularly T (frameOf m).F (frameOf m).Z ∧ ActsRegularly T (frameOf m).A (frameOf m).F := by
  have h0 : IsSylowIn 3 (centEl (g23T5 m) (frameOf m).z) (zpowers (uE m 5)) :=
    sylow3 (k3_mem_C m) (k3_order m) (n := 64) (by rw [card_C]) (by norm_num)
  refine forall_isSylowIn_of_one h0 ⟨F_reg m, A_reg m⟩ (fun g hg h => ⟨?_, ?_⟩)
  · exact actsRegularly_conj (T5_le_norm_F m hg.1) (C_le_norm_Z m hg) h.1
  · exact actsRegularly_conj (C_norm_A m hg) (T5_le_norm_F m hg.1) h.2

theorem facts (m : G23Model G) : G23T5Facts m :=
  ⟨F_normal m, F_isE m, card_T5 m, cen_B m, cen_B_isE m, card_B m, card_normIn_B m, B_S3 m,
    B_sylow m, F_GL3 m, S_sylow m, S_no_complement m, F_S3 m, F_sylow m, Y1_conj m,
    nine_conj_E m⟩

end CFSG.KD.G2Three.Sec1.T5Glue

end
