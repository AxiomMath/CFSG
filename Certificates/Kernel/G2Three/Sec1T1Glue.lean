module

public import Certificates.Kernel.G2Three.Sec1T1Checks
public import Certificates.Kernel.G2Three.Sec1T1Checks2
public import Certificates.Kernel.G2Three.Sec1T5Glue
public import CFSG.Certificates.Kernel.G2Three.Sec1T1Sound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T1Facts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelL
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1.T1Glue

open Subgroup CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KC.G2Three CFSG.KC.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.KD.G2Three.Sec1.T5Glue CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (m : G23Model G)

@[expose] def g1W (s : ℕ) : List ℕ := [u1W, b1W, u2W, b2W, h0W, a1W, a2W].getD s []

@[expose] def gen1 (s : ℕ) : G :=
  [(frameOf m).u₁, (frameOf m).b₁, (frameOf m).u₂, (frameOf m).b₂, (frameOf m).h₀, (frameOf m).a₁,
    (frameOf m).a₂].getD s 1

theorem isW_g1W {s : ℕ} (hs : s < 7) : IsW (g1W s) := by
  interval_cases s <;> (unfold IsW; decide)

theorem gen1_eq {s : ℕ} (hs : s < 7) : gen1 m s = wordG m (g1W s) := by
  interval_cases s
  · exact u1_eq m
  · exact b1_eq m
  · exact u2_eq m
  · exact b2_eq m
  · exact h0_eq m
  · exact a1_eq m
  · exact a2_eq m

theorem r1U_gen : ∀ s < 7, R1U s = wD (g1W s) := by
  intro s hs
  interval_cases s
  all_goals exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem enc_gen1 {s : ℕ} (hs : s < 7) : Enc m.ρ (R1U s) (gen1 m s) := by
  rw [gen1_eq m hs, r1U_gen s hs]
  exact enc_word m (isW_g1W hs)

@[expose] def defs1 : List (ℕ × ℕ) :=
  [(0, 0), (1, 2), (3, 4), (1, 1), (5, 6), (1, 3), (5, 1), (14, 6), (5, 3), (1, 6), (2, 2),
    (8, 2), (19, 3), (0, 1), (21, 4), (22, 0), (11, 4), (5, 11), (1, 11), (6, 11), (3, 11),
    (12, 11), (13, 11), (15, 11), (0, 2), (0, 18), (8, 18), (6, 3), (35, 5)]

@[expose] def uE1 (i : ℕ) : G :=
  (defs1.foldl stepU (((List.range 7).map (gen1 m)) ++ [1])).getD i 1

theorem r1U_defs : ∀ j < 29, (defs1.getD j (0, 0)).1 < j + 8 ∧ (defs1.getD j (0, 0)).2 < j + 8 ∧
    R1U (j + 8) = MULP (R1U (defs1.getD j (0, 0)).1) (R1U (defs1.getD j (0, 0)).2) := by
  intro j hj
  interval_cases j
  all_goals exact ⟨by decide, by decide, Nat.eq_of_beq_eq_true (by quickRfl)⟩

private theorem enc_fold : ∀ (ds : List (ℕ × ℕ)) (k : ℕ) (acc : List G), acc.length = k →
    (∀ i < k, Enc m.ρ (R1U i) (acc.getD i 1)) →
    (∀ j < ds.length, (ds.getD j (0, 0)).1 < k + j ∧ (ds.getD j (0, 0)).2 < k + j ∧
      R1U (k + j) = MULP (R1U (ds.getD j (0, 0)).1) (R1U (ds.getD j (0, 0)).2)) →
    ∀ i < k + ds.length, Enc m.ρ (R1U i) ((ds.foldl stepU acc).getD i 1)
  | [], k, acc, _, hacc, _ => by simpa using hacc
  | d :: ds, k, acc, hk, hacc, hds => by
    have h0 := hds 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    have hacc' : ∀ i < k + 1, Enc m.ρ (R1U i) ((stepU acc d).getD i 1) := by
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

theorem r1_ones : R1U 7 = ONEP ∧ R1H 0 = ONEP ∧ R1K1 0 = ONEP ∧ R1K2 0 = ONEP ∧ R1Q1 0 = ONEP ∧
    R1Q2 0 = ONEP ∧ R1S 0 = ONEP ∧ R1A 0 = ONEP ∧ R1M 0 = ONEP ∧ R1KY 0 = 28 ∧ R1PY 0 = 2340 ∧
    R1PI 0 = 2340 := by
  have h := r1_one
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem enc_uE1 {i : ℕ} (hi : i < 37) : Enc m.ρ (R1U i) (uE1 m i) := by
  have hl : defs1.length = 29 := rfl
  refine enc_fold m defs1 8 _ (by simp) (fun i hi => ?_) (fun j hj => ?_) i (by rw [hl]; omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, List.getElem_range]
      exact enc_gen1 m hi
    · rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
      rw [r1_ones.1]
      exact enc_one m.ρ
  · rw [Nat.add_comm 8 j]
    exact r1U_defs j (by rw [hl] at hj; exact hj)

theorem g23H_eq : g23H m = closure {(frameOf m).u₁, (frameOf m).b₁, (frameOf m).u₂, (frameOf m).b₂,
    (frameOf m).h₀} := by
  simp only [g23H, SFrame.K₁, SFrame.K₂]
  rw [← Subgroup.closure_union, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem gen1_mem {s : ℕ} : gen1 m s ∈ g23H m := by
  rw [g23H_eq]
  rcases Nat.lt_or_ge s 7 with hs | hs
  · interval_cases s
    · exact subset_closure (by simp [gen1])
    · exact subset_closure (by simp [gen1])
    · exact subset_closure (by simp [gen1])
    · exact subset_closure (by simp [gen1])
    · exact subset_closure (by simp [gen1])
    · have e : gen1 m 5 = (frameOf m).u₁ * (frameOf m).b₁ ^ 3 * (frameOf m).u₁⁻¹ := rfl
      rw [e]
      exact mul_mem (mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _))
        (inv_mem (subset_closure (by simp)))
    · have e : gen1 m 6 = (frameOf m).u₂ * (frameOf m).b₂ ^ 3 * (frameOf m).u₂⁻¹ := rfl
      rw [e]
      exact mul_mem (mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _))
        (inv_mem (subset_closure (by simp)))
  · have e : gen1 m s = 1 := by
      simp only [gen1]
      rw [List.getD_eq_default _ _ (by simp; omega)]
    rw [e]
    exact one_mem _

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

theorem uE1_mem (i : ℕ) : uE1 m i ∈ g23H m := by
  refine getD_mem (mem_fold _ defs1 _ ?_) i
  intro x hx
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hx
  rcases hx with ⟨s, -, rfl⟩ | rfl
  · exact gen1_mem m
  · exact (g23H m).one_mem

attribute [local irreducible] uE1

theorem uE1_gen {s : ℕ} (hs : s < 7) : uE1 m s = gen1 m s :=
  enc_unique m.inj (enc_uE1 m (by omega)) (enc_gen1 m hs)

theorem uE1_seven : uE1 m 7 = 1 :=
  enc_unique m.inj (enc_uE1 m (by norm_num)) (by rw [r1_ones.1]; exact enc_one m.ρ)

theorem rl (q a b c d : ℕ) (h : (Nat.beq (R1RA q) a && Nat.beq (R1RB q) b && Nat.beq (R1RC q) c &&
    Nat.beq (R1RD q) d && Nat.blt q 67 && Nat.blt a 37 && Nat.blt b 37 && Nat.blt c 37 &&
    Nat.blt d 37) = true) : uE1 m a * uE1 m b = uE1 m c * uE1 m d := by
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hq⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  have e : MULP (R1U (R1RA q)) (R1U (R1RB q)) = MULP (R1U (R1RC q)) (R1U (R1RD q)) :=
    eqK_at r1_rel (by norm_num) q hq
  rw [ha, hb, hc, hd] at e
  exact mul_eq_of_MULP m.inj (enc_uE1 m h1) (enc_uE1 m h2) (enc_uE1 m h3) (enc_uE1 m h4) e

theorem rl' (q a b c : ℕ) (h : (Nat.beq (R1RA q) a && Nat.beq (R1RB q) b && Nat.beq (R1RC q) c &&
    Nat.beq (R1RD q) 7 && Nat.blt q 67 && Nat.blt a 37 && Nat.blt b 37 && Nat.blt c 37 &&
    Nat.blt 7 37) = true) : uE1 m a * uE1 m b = uE1 m c := by
  have e := rl m q a b c 7 h
  rwa [uE1_seven, mul_one] at e

theorem uE1_u1 : uE1 m 0 = (frameOf m).u₁ := uE1_gen m (s := 0) (by norm_num)
theorem uE1_b1 : uE1 m 1 = (frameOf m).b₁ := uE1_gen m (s := 1) (by norm_num)
theorem uE1_u2 : uE1 m 2 = (frameOf m).u₂ := uE1_gen m (s := 2) (by norm_num)
theorem uE1_b2 : uE1 m 3 = (frameOf m).b₂ := uE1_gen m (s := 3) (by norm_num)
theorem uE1_h0 : uE1 m 4 = (frameOf m).h₀ := uE1_gen m (s := 4) (by norm_num)
theorem uE1_a1 : uE1 m 5 = (frameOf m).a₁ := uE1_gen m (s := 5) (by norm_num)
theorem uE1_a2 : uE1 m 6 = (frameOf m).a₂ := uE1_gen m (s := 6) (by norm_num)

theorem uE1_z : uE1 m 11 = (frameOf m).z := by
  rw [← rl' m 3 1 1 11 (by quickRfl), uE1_b1, SFrame.z, pow_two]

theorem tabH : TabOf m.ρ R1H 576 (closure ((fun s => uE1 m (R1HG s)) '' {s | s < 3}) : Set G) := by
  have key : ∀ i lo, closP R1H (fun s => R1U (R1HG s)) R1HPOS 576 3 lo 432 7 = true → lo ≤ i →
      i < lo + 432 → R1HPOS i < 576 ∧ R1H (R1HPOS i) = MULP (R1H (i / 3)) (R1U (R1HG (i % 3))) := by
    intro i lo h h1 h2
    have := closP_at h (by norm_num) (i - lo) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact this
  have hcl : ∀ i < 576 * 3,
      R1HPOS i < 576 ∧ R1H (R1HPOS i) = MULP (R1H (i / 3)) (R1U (R1HG (i % 3))) := by
    intro i hi
    by_cases h0 : i < 432
    · exact key i 0 r1_closH0 (by omega) (by omega)
    by_cases h1 : i < 864
    · exact key i 432 r1_closH1 (by omega) (by omega)
    by_cases h2 : i < 1296
    · exact key i 864 r1_closH2 (by omega) (by omega)
    · exact key i 1296 r1_closH3 (by omega) (by omega)
  have hG : ∀ s < 3, R1HG s < 37 := by
    intro s hs
    interval_cases s <;> exact Nat.blt_eq.mp (by quickRfl)
  exact tab_closure m.inj (Gd := fun s => R1U (R1HG s)) (by norm_num)
    (fun s hs => enc_uE1 m (hG s hs)) r1_ones.2.1 hcl (parK_at r1_parH (by norm_num))

theorem uE1_mem_tabH {s : ℕ} (hs : s < 8) :
    uE1 m s ∈ closure ((fun s => uE1 m (R1HG s)) '' {s | s < 3}) := by
  have h := idxK_at (Bool.and_eq_true _ _ ▸ r1_genH).1 (by norm_num) s hs
  exact mem_of_tabOf m.inj (tabH m) h.1 (by rw [h.2]; exact enc_uE1 m (by omega))

theorem H_eq : closure ((fun s => uE1 m (R1HG s)) '' {s | s < 3}) = g23H m := by
  apply le_antisymm
  · rw [closure_le]
    rintro x ⟨s, -, rfl⟩
    exact uE1_mem m _
  · rw [g23H_eq, closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [← uE1_u1]
      exact uE1_mem_tabH m (by norm_num)
    · rw [← uE1_b1]
      exact uE1_mem_tabH m (by norm_num)
    · rw [← uE1_u2]
      exact uE1_mem_tabH m (by norm_num)
    · rw [← uE1_b2]
      exact uE1_mem_tabH m (by norm_num)
    · rw [← uE1_h0]
      exact uE1_mem_tabH m (by norm_num)

theorem tabH' : TabOf m.ρ R1H 576 ((g23H m : Subgroup G) : Set G) := by
  rw [← H_eq]
  exact tabH m

theorem H_inj : ∀ i < 576, ∀ j < 576, R1H i = R1H j → i = j := sort_inj r1_sortH (by norm_num)

theorem card_H : Nat.card (g23H m) = 576 := tab_card m.inj (tabH' m) (H_inj)

theorem z_ne_one : (frameOf m).z ≠ 1 := by
  have h := neK_at r1_nrel (by norm_num) 2 (by norm_num)
  have e2 : R1NA 2 = 11 ∧ R1NB 2 = 7 ∧ R1NC 2 = 7 ∧ R1ND 2 = 7 :=
    ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  rw [e2.1, e2.2.1, e2.2.2.1, e2.2.2.2] at h
  have := mul_ne_of_MULP (enc_uE1 m (i := 11) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num))
    (enc_uE1 m (i := 7) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num)) h
  rw [uE1_seven, mul_one, mul_one, uE1_z] at this
  exact this

theorem z_sq : (frameOf m).z * (frameOf m).z = 1 := by
  rw [← uE1_z, rl' m 31 11 11 7 (by quickRfl), uE1_seven]

theorem z_order : orderOf (frameOf m).z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact z_sq m) (z_ne_one m)

theorem z_comm_gen : ∀ x ∈ ({(frameOf m).u₁, (frameOf m).b₁, (frameOf m).u₂, (frameOf m).b₂,
    (frameOf m).h₀} : Set G), (frameOf m).z * x = x * (frameOf m).z := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [← uE1_z]
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [← uE1_u1]
    exact rl m 40 11 0 0 11 (by quickRfl)
  · rw [← uE1_b1]
    exact rl m 41 11 1 1 11 (by quickRfl)
  · rw [← uE1_u2]
    exact rl m 42 11 2 2 11 (by quickRfl)
  · rw [← uE1_b2]
    exact rl m 43 11 3 3 11 (by quickRfl)
  · rw [← uE1_h0]
    exact rl m 44 11 4 4 11 (by quickRfl)

theorem H_le_cent_z : g23H m ≤ centralizer ({(frameOf m).z} : Set G) := by
  rw [g23H_eq, closure_le]
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (z_comm_gen m x hx).symm

theorem H_cent_z : ∀ h ∈ g23H m, h * (frameOf m).z = (frameOf m).z * h :=
  fun h hh => mem_centralizer_singleton_iff.mp (H_le_cent_z m hh)

theorem uE1_a1a2 : uE1 m 12 = (frameOf m).a₁ * (frameOf m).a₂ := by
  rw [← rl' m 4 5 6 12 (by quickRfl), uE1_a1, uE1_a2]

theorem uE1_b1b2 : uE1 m 13 = (frameOf m).b₁ * (frameOf m).b₂ := by
  rw [← rl' m 5 1 3 13 (by quickRfl), uE1_b1, uE1_b2]

theorem uE1_a1b1a2 : uE1 m 15 = (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂ := by
  rw [← rl' m 7 14 6 15 (by quickRfl), ← rl' m 6 5 1 14 (by quickRfl), uE1_a1, uE1_b1, uE1_a2]

theorem uE1_a1b2 : uE1 m 16 = (frameOf m).a₁ * (frameOf m).b₂ := by
  rw [← rl' m 8 5 3 16 (by quickRfl), uE1_a1, uE1_b2]

theorem uE1_b1a2 : uE1 m 17 = (frameOf m).b₁ * (frameOf m).a₂ := by
  rw [← rl' m 9 1 6 17 (by quickRfl), uE1_b1, uE1_a2]

theorem basis3 {X Gd SRT SRI : ℕ → ℕ} (hG : ∀ s < 3, Gd s < 37)
    (hc : ∀ s < 3, ∀ t < 3, uE1 m (Gd s) * uE1 m (Gd t) = uE1 m (Gd t) * uE1 m (Gd s))
    (hs : ∀ s < 3, uE1 m (Gd s) * uE1 m (Gd s) = 1)
    (h : (basisK X (fun s => R1U (Gd s)) 3 8 1 && sortK X SRT SRI 8 1) = true) :
    TabOf m.ρ X 8 (closure ((fun s => uE1 m (Gd s)) '' {s | s < 3}) : Set G) ∧
      Nat.card (closure ((fun s => uE1 m (Gd s)) '' {s | s < 3})) = 8 ∧
      ∀ c < 8, Enc m.ρ (X c) (pwG (fun s => uE1 m (Gd s)) 3 c) := by
  simp only [Bool.and_eq_true] at h
  have hb := basisK_at h.1 (by norm_num)
  have hg : ∀ s < 3, Enc m.ρ (R1U (Gd s)) (uE1 m (Gd s)) := fun s hs' => enc_uE1 m (hG s hs')
  have ht := basis_tab (Gd := fun s => R1U (Gd s)) hg hc hs hb
  refine ⟨ht, tab_card m.inj ht (sort_inj h.2 (by norm_num)), fun c hc8 => ?_⟩
  rw [hb c hc8]
  exact enc_pwP m.ρ hg c

theorem image3 {Gd : ℕ → ℕ} {a b c : ℕ} (h0 : Gd 0 = a) (h1 : Gd 1 = b) (h2 : Gd 2 = c) :
    (fun s => uE1 m (Gd s)) '' {s | s < 3} = {uE1 m a, uE1 m b, uE1 m c} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    interval_cases s
    · exact Or.inl (by rw [h0])
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inr (Or.inr (by rw [h2]))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by rw [h0]⟩
    · exact ⟨1, by norm_num, by rw [h1]⟩
    · exact ⟨2, by norm_num, by rw [h2]⟩

theorem gens3 {Gd : ℕ → ℕ} {a b c : ℕ} (h0 : Gd 0 = a) (h1 : Gd 1 = b) (h2 : Gd 2 = c)
    (ia : uE1 m a * uE1 m a = 1) (ib : uE1 m b * uE1 m b = 1) (ic : uE1 m c * uE1 m c = 1)
    (cab : uE1 m a * uE1 m b = uE1 m b * uE1 m a) (cac : uE1 m a * uE1 m c = uE1 m c * uE1 m a)
    (cbc : uE1 m b * uE1 m c = uE1 m c * uE1 m b) :
    (∀ s < 3, ∀ t < 3, uE1 m (Gd s) * uE1 m (Gd t) = uE1 m (Gd t) * uE1 m (Gd s)) ∧
      ∀ s < 3, uE1 m (Gd s) * uE1 m (Gd s) = 1 := by
  refine ⟨fun s hs t ht => ?_, fun s hs => ?_⟩
  · interval_cases s <;> interval_cases t <;> simp only [h0, h1, h2, cab, cac, cbc]
  · interval_cases s <;> simp only [h0, h1, h2, ia, ib, ic]

theorem r1EG : R1EG 0 = 13 ∧ R1EG 1 = 15 ∧ R1EG 2 = 11 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem r1FG : R1FG 0 = 12 ∧ R1FG 1 = 13 ∧ R1FG 2 = 11 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem lt37 {Gd : ℕ → ℕ} {a b c : ℕ} (h0 : Gd 0 = a) (h1 : Gd 1 = b) (h2 : Gd 2 = c)
    (ha : a < 37) (hb : b < 37) (hc : c < 37) : ∀ s < 3, Gd s < 37 := by
  intro s hs
  interval_cases s <;> simp only [h0, h1, h2] <;> assumption

theorem E_gens :
    (∀ s < 3, ∀ t < 3, uE1 m (R1EG s) * uE1 m (R1EG t) = uE1 m (R1EG t) * uE1 m (R1EG s)) ∧
      ∀ s < 3, uE1 m (R1EG s) * uE1 m (R1EG s) = 1 := gens3 m (Gd := R1EG) r1EG.1 r1EG.2.1 r1EG.2.2
  (by rw [rl' m 46 13 13 7 (by quickRfl), uE1_seven])
  (by rw [rl' m 47 15 15 7 (by quickRfl), uE1_seven])
  (by rw [rl' m 31 11 11 7 (by quickRfl), uE1_seven])
  (rl m 49 13 15 15 13 (by quickRfl)) (rl m 57 13 11 11 13 (by quickRfl))
  (rl m 58 15 11 11 15 (by quickRfl))

theorem F_gens :
    (∀ s < 3, ∀ t < 3, uE1 m (R1FG s) * uE1 m (R1FG t) = uE1 m (R1FG t) * uE1 m (R1FG s)) ∧
      ∀ s < 3, uE1 m (R1FG s) * uE1 m (R1FG s) = 1 := gens3 m (Gd := R1FG) r1FG.1 r1FG.2.1 r1FG.2.2
  (by rw [rl' m 45 12 12 7 (by quickRfl), uE1_seven])
  (by rw [rl' m 46 13 13 7 (by quickRfl), uE1_seven])
  (by rw [rl' m 31 11 11 7 (by quickRfl), uE1_seven])
  (rl m 48 12 13 13 12 (by quickRfl)) (rl m 56 12 11 11 12 (by quickRfl))
  (rl m 57 13 11 11 13 (by quickRfl))

theorem tabE : TabOf m.ρ R1E 8 (closure ((fun s => uE1 m (R1EG s)) '' {s | s < 3}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1EG s)) '' {s | s < 3})) = 8 ∧
    ∀ c < 8, Enc m.ρ (R1E c) (pwG (fun s => uE1 m (R1EG s)) 3 c) :=
  basis3 m (lt37 r1EG.1 r1EG.2.1 r1EG.2.2 (by norm_num) (by norm_num) (by norm_num))
    (E_gens m).1 (E_gens m).2 r1_E

theorem tabF : TabOf m.ρ R1F 8 (closure ((fun s => uE1 m (R1FG s)) '' {s | s < 3}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1FG s)) '' {s | s < 3})) = 8 ∧
    ∀ c < 8, Enc m.ρ (R1F c) (pwG (fun s => uE1 m (R1FG s)) 3 c) :=
  basis3 m (lt37 r1FG.1 r1FG.2.1 r1FG.2.2 (by norm_num) (by norm_num) (by norm_num))
    (F_gens m).1 (F_gens m).2 r1_F

theorem E_eq : closure ((fun s => uE1 m (R1EG s)) '' {s | s < 3}) = (frameOf m).E := by
  rw [image3 m r1EG.1 r1EG.2.1 r1EG.2.2, uE1_b1b2, uE1_a1b1a2, uE1_z]
  rfl

theorem F_eq : closure ((fun s => uE1 m (R1FG s)) '' {s | s < 3}) = (frameOf m).F := by
  rw [image3 m r1FG.1 r1FG.2.1 r1FG.2.2, uE1_a1a2, uE1_b1b2, uE1_z]
  rfl

theorem card_E : Nat.card (frameOf m).E = 8 := by
  rw [← E_eq]
  exact (tabE m).2.1

theorem elemAb_E : IsElemAbelian 2 (frameOf m).E := by
  rw [← E_eq]
  refine isElemAbelian_closure ?_ ?_
  · rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
    exact (E_gens m).1 s hs t ht
  · rintro a ⟨s, hs, rfl⟩
    exact (E_gens m).2 s hs

theorem E_le_H : (frameOf m).E ≤ g23H m := by
  rw [← E_eq, closure_le]
  rintro x ⟨s, -, rfl⟩
  exact uE1_mem m _

theorem F_le_H : (frameOf m).F ≤ g23H m := by
  rw [← F_eq, closure_le]
  rintro x ⟨s, -, rfl⟩
  exact uE1_mem m _

theorem centIn_H_eq {Gd : ℕ → ℕ} {g : ℕ → G} {k hi : ℕ} {X : Subgroup G}
    (hg : ∀ s < k, Enc m.ρ (Gd s) (g s)) (hX : X = closure (g '' {s | s < k}))
    (hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXH : X ≤ g23H m) (hi576 : 576 ≤ 64 * hi)
    (hc : cntK R1H Gd k 576 hi = Nat.card X) : centIn (g23H m) X = X := by
  have h := cntK_card m.inj (tabH' m) (H_inj) hg hi576
  rw [hc] at h
  have e : centIn (g23H m) X = g23H m ⊓ centralizer (g '' {s | s < k}) := by
    rw [centIn, hX, cent_closure]
  have hle : X ≤ centIn (g23H m) X := fun x hx =>
    ⟨hXH hx, mem_centralizer_iff.mpr fun y hy => hab y hy x hx⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [e, ← h]

theorem E_comm : ∀ x ∈ (frameOf m).E, ∀ y ∈ (frameOf m).E, x * y = y * x := by
  rw [← E_eq]
  refine closure_comm ?_
  rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
  exact (E_gens m).1 s hs t ht

theorem centIn_H_E : centIn (g23H m) (frameOf m).E = (frameOf m).E := by
  refine centIn_H_eq m (Gd := fun s => R1U (R1EG s)) (g := fun s => uE1 m (R1EG s)) (k := 3) (hi := 9)
    (fun s hs => enc_uE1 m (lt37 r1EG.1 r1EG.2.1 r1EG.2.2 (by norm_num) (by norm_num) (by norm_num)
      s hs)) (E_eq m).symm (E_comm m) (E_le_H m) (by norm_num) ?_
  rw [card_E, Nat.eq_of_beq_eq_true r1_cE]

theorem F_comm : ∀ x ∈ (frameOf m).F, ∀ y ∈ (frameOf m).F, x * y = y * x := by
  rw [← F_eq]
  refine closure_comm ?_
  rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
  exact (F_gens m).1 s hs t ht

theorem card_F : Nat.card (frameOf m).F = 8 := by
  rw [← F_eq]
  exact (tabF m).2.1

theorem centIn_H_F : centIn (g23H m) (frameOf m).F = (frameOf m).F := by
  refine centIn_H_eq m (Gd := fun s => R1U (R1FG s)) (g := fun s => uE1 m (R1FG s)) (k := 3) (hi := 9)
    (fun s hs => enc_uE1 m (lt37 r1FG.1 r1FG.2.1 r1FG.2.2 (by norm_num) (by norm_num) (by norm_num)
      s hs)) (F_eq m).symm (F_comm m) (F_le_H m) (by norm_num) ?_
  rw [card_F, Nat.eq_of_beq_eq_true r1_cF]

theorem sigma_rho : m.ρ (frameOf m).σ = wanti 1 1 := m.ρ_gS

theorem sigma_sq : (frameOf m).σ * (frameOf m).σ = 1 := m.gS_sq

theorem enc_sig {x : ℕ} {g : G} (hx : Enc m.ρ x g) :
    Enc m.ρ (SWP x) ((frameOf m).σ * g * (frameOf m).σ⁻¹) :=
  enc_SWP m.ρ (sigma_rho m) (sigma_sq m) hx

theorem sw (q a b : ℕ) (h : (Nat.beq (R1SWA q) a && Nat.beq (R1SWB q) b && Nat.blt q 11 &&
    Nat.blt a 37 && Nat.blt b 37) = true) :
    (frameOf m).σ * uE1 m a * (frameOf m).σ⁻¹ = uE1 m b := by
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hq⟩, h1⟩, h2⟩ := h
  have e : SWP (R1U (R1SWA q)) = R1U (R1SWB q) :=
    Nat.eq_of_beq_eq_true (allBelow_g2 r1_swp (by norm_num) q hq)
  rw [ha, hb] at e
  exact enc_unique m.inj (enc_sig m (enc_uE1 m h1)) (e ▸ enc_uE1 m h2)

theorem sigma_K1 : conjSub (frameOf m).σ (frameOf m).K₁ = (frameOf m).K₂ := by
  have e1 := sw m 0 0 2 (by quickRfl)
  have e2 := sw m 2 1 3 (by quickRfl)
  rw [uE1_u1, uE1_u2] at e1
  rw [uE1_b1, uE1_b2] at e2
  rw [SFrame.K₁, SFrame.K₂, conjSub_pair, e1, e2]

theorem sigma_comm_of {x : G} (h : (frameOf m).σ * x * (frameOf m).σ⁻¹ = x) :
    (frameOf m).σ * x = x * (frameOf m).σ := by
  rw [← h, inv_mul_cancel_right, h]

theorem F_cent_sigma : ∀ f ∈ (frameOf m).F, (frameOf m).σ * f = f * (frameOf m).σ := by
  have hle : (frameOf m).F ≤ centralizer ({(frameOf m).σ} : Set G) := by
    rw [← F_eq, image3 m r1FG.1 r1FG.2.1 r1FG.2.2, closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    refine mem_centralizer_singleton_iff.mpr ?_
    rcases hx with rfl | rfl | rfl
    · exact (sigma_comm_of m (sw m 6 12 12 (by quickRfl))).symm
    · exact (sigma_comm_of m (sw m 7 13 13 (by quickRfl))).symm
    · exact (sigma_comm_of m (sw m 5 11 11 (by quickRfl))).symm
  intro f hf
  exact (mem_centralizer_singleton_iff.mp (hle hf)).symm

theorem K_comm : ∀ u ∈ (frameOf m).K₁, ∀ v ∈ (frameOf m).K₂, u * v = v * u := by
  have c02 := rl m 36 0 2 2 0 (by quickRfl)
  have c03 := rl m 37 0 3 3 0 (by quickRfl)
  have c12 := rl m 38 1 2 2 1 (by quickRfl)
  have c13 := rl m 39 1 3 3 1 (by quickRfl)
  rw [uE1_u1, uE1_u2] at c02
  rw [uE1_u1, uE1_b2] at c03
  rw [uE1_b1, uE1_u2] at c12
  rw [uE1_b1, uE1_b2] at c13
  have h2 : (frameOf m).K₂ ≤ centralizer ((frameOf m).K₁ : Set G) := by
    rw [SFrame.K₁, cent_closure, SFrame.K₂, closure_le]
    intro v hv
    refine mem_centralizer_iff.mpr ?_
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [c02, c03, c12, c13]
  intro u hu v hv
  exact (mem_centralizer_iff.mp (h2 hv) u hu)

theorem u_order3 {u : G} (h1 : u * (u * u) = 1) (hne : u ≠ 1) : orderOf u = 3 := by
  refine orderOf_eq_prime ?_ hne
  rw [pow_succ, pow_two, mul_assoc]
  calc u * (u * u) = 1 := h1

theorem u1_order : orderOf (frameOf m).u₁ = 3 := by
  have h8 := rl' m 0 0 0 8 (by quickRfl)
  have h := rl' m 29 0 8 7 (by quickRfl)
  rw [← h8, uE1_seven, uE1_u1] at h
  have hne : (frameOf m).u₁ ≠ 1 := by
    have hn := neK_at r1_nrel (by norm_num) 0 (by norm_num)
    have e : R1NA 0 = 0 ∧ R1NB 0 = 7 ∧ R1NC 0 = 7 ∧ R1ND 0 = 7 :=
      ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
        Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2] at hn
    have := mul_ne_of_MULP (enc_uE1 m (i := 0) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num))
      (enc_uE1 m (i := 7) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num)) hn
    rwa [uE1_seven, mul_one, mul_one, uE1_u1] at this
  exact u_order3 h hne

theorem u2_order : orderOf (frameOf m).u₂ = 3 := by
  have h18 := rl' m 10 2 2 18 (by quickRfl)
  have h := rl' m 30 2 18 7 (by quickRfl)
  rw [← h18, uE1_seven, uE1_u2] at h
  have hne : (frameOf m).u₂ ≠ 1 := by
    have hn := neK_at r1_nrel (by norm_num) 1 (by norm_num)
    have e : R1NA 1 = 2 ∧ R1NB 1 = 7 ∧ R1NC 1 = 7 ∧ R1ND 1 = 7 :=
      ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
        Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2] at hn
    have := mul_ne_of_MULP (enc_uE1 m (i := 2) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num))
      (enc_uE1 m (i := 7) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num)) hn
    rwa [uE1_seven, mul_one, mul_one, uE1_u2] at this
  exact u_order3 h hne

theorem inv_zpowers {h u : G} (hu : u * (u * u) = 1) (hh : h * u = (u * u) * h) :
    ∀ y ∈ zpowers u, h * y * h⁻¹ = y⁻¹ := by
  have hinv : u⁻¹ = u * u := (eq_inv_of_mul_eq_one_right hu).symm
  have hc : h * u * h⁻¹ = u⁻¹ := by rw [hh, mul_inv_cancel_right, hinv]
  rintro y ⟨n, rfl⟩
  change h * u ^ n * h⁻¹ = (u ^ n)⁻¹
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hc, inv_zpow]

theorem h0_inv1 : ∀ y ∈ (frameOf m).X₁, (frameOf m).h₀ * y * (frameOf m).h₀⁻¹ = y⁻¹ := by
  have h8 := rl' m 0 0 0 8 (by quickRfl)
  have h := rl' m 29 0 8 7 (by quickRfl)
  have hh := rl m 34 4 0 8 4 (by quickRfl)
  rw [← h8, uE1_seven, uE1_u1] at h
  rw [← h8, uE1_h0, uE1_u1] at hh
  exact inv_zpowers h hh

theorem h0_inv2 : ∀ y ∈ (frameOf m).X₂, (frameOf m).h₀ * y * (frameOf m).h₀⁻¹ = y⁻¹ := by
  have h18 := rl' m 10 2 2 18 (by quickRfl)
  have h := rl' m 30 2 18 7 (by quickRfl)
  have hh := rl m 35 4 2 18 4 (by quickRfl)
  rw [← h18, uE1_seven, uE1_u2] at h
  rw [← h18, uE1_h0, uE1_u2] at hh
  exact inv_zpowers h hh

theorem r1KG : R1K1G 0 = 0 ∧ R1K1G 1 = 1 ∧ R1K2G 0 = 2 ∧ R1K2G 1 = 3 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem image2 {Gd : ℕ → ℕ} {a b : ℕ} (h0 : Gd 0 = a) (h1 : Gd 1 = b) :
    (fun s => uE1 m (Gd s)) '' {s | s < 2} = {uE1 m a, uE1 m b} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    interval_cases s
    · exact Or.inl (by rw [h0])
    · exact Or.inr (by rw [h1])
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by rw [h0]⟩
    · exact ⟨1, by norm_num, by rw [h1]⟩

theorem tabK1 : TabOf m.ρ R1K1 24 (closure ((fun s => uE1 m (R1K1G s)) '' {s | s < 2}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1K1G s)) '' {s | s < 2})) = 24 ∧
    ∀ i < 24, ∀ j < 24, R1K1 i = R1K1 j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1K1G s)) (g := fun s => uE1 m (R1K1G s)) (by norm_num)
    (fun s hs => enc_uE1 m (by interval_cases s <;> simp [r1KG.1, r1KG.2.1])) r1_ones.2.2.1 r1_K1
    (by norm_num) (by norm_num) (by norm_num)

theorem tabK2 : TabOf m.ρ R1K2 24 (closure ((fun s => uE1 m (R1K2G s)) '' {s | s < 2}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1K2G s)) '' {s | s < 2})) = 24 ∧
    ∀ i < 24, ∀ j < 24, R1K2 i = R1K2 j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1K2G s)) (g := fun s => uE1 m (R1K2G s)) (by norm_num)
    (fun s hs => enc_uE1 m (by interval_cases s <;> simp [r1KG.2.2.1, r1KG.2.2.2]))
    r1_ones.2.2.2.1 r1_K2 (by norm_num) (by norm_num) (by norm_num)

theorem K1_eq : closure ((fun s => uE1 m (R1K1G s)) '' {s | s < 2}) = (frameOf m).K₁ := by
  rw [image2 m r1KG.1 r1KG.2.1, uE1_u1, uE1_b1]
  rfl

theorem K2_eq : closure ((fun s => uE1 m (R1K2G s)) '' {s | s < 2}) = (frameOf m).K₂ := by
  rw [image2 m r1KG.2.2.1 r1KG.2.2.2, uE1_u2, uE1_b2]
  rfl

theorem card_K1 : Nat.card (frameOf m).K₁ = 24 := by
  rw [← K1_eq]
  exact (tabK1 m).2.1

theorem card_K2 : Nat.card (frameOf m).K₂ = 24 := by
  rw [← K2_eq]
  exact (tabK2 m).2.1

theorem sylow3_of_card {K X : Subgroup G} (hXK : X ≤ K) (hK : Nat.card K = 24)
    (hX : Nat.card X = 3) : IsSylowIn 3 K X := by
  refine ⟨hXK, IsPGroup.of_card (n := 1) (by rw [hX]; norm_num), ?_⟩
  have h := relIndex_mul_card (H := X) (K := K)
  rw [inf_of_le_left hXK, hX, hK] at h
  have h8 : X.relIndex K = 8 := by omega
  rw [h8]
  norm_num

theorem X1_sylow : IsSylowIn 3 (frameOf m).K₁ (frameOf m).X₁ := by
  refine sylow3_of_card ?_ (card_K1 m) ?_
  · rw [SFrame.X₁, zpowers_le, SFrame.K₁]
    exact subset_closure (by simp)
  · rw [SFrame.X₁, Nat.card_zpowers, u1_order]

theorem X2_sylow : IsSylowIn 3 (frameOf m).K₂ (frameOf m).X₂ := by
  refine sylow3_of_card ?_ (card_K2 m) ?_
  · rw [SFrame.X₂, zpowers_le, SFrame.K₂]
    exact subset_closure (by simp)
  · rw [SFrame.X₂, Nat.card_zpowers, u2_order]

theorem H_gen_uE1 {x : G} (hx : x ∈ ({(frameOf m).u₁, (frameOf m).b₁, (frameOf m).u₂,
    (frameOf m).b₂, (frameOf m).h₀} : Set G)) : ∃ a < 5, uE1 m a = x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, uE1_u1 m⟩
  · exact ⟨1, by norm_num, uE1_b1 m⟩
  · exact ⟨2, by norm_num, uE1_u2 m⟩
  · exact ⟨3, by norm_num, uE1_b2 m⟩
  · exact ⟨4, by norm_num, uE1_h0 m⟩

theorem H_le_normalizer {X gK W : ℕ → ℕ} {n k : ℕ} {K : Subgroup G}
    (hK : K = closure ((fun c => uE1 m (gK c)) '' {c | c < k})) (htab : TabOf m.ρ X n (K : Set G))
    (hgK : ∀ c < k, gK c < 37)
    (hrec : ∀ q < 5 * k, MULP (R1U (q / k)) (R1U (gK (q % k))) = MULP (X (W q)) (R1U (q / k)) ∧
      W q < n) : g23H m ≤ normalizer (K : Set G) := by
  rw [g23H_eq, hK]
  refine closure_le_normalizer ?_
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := H_gen_uE1 m hs
  obtain ⟨c, hc, rfl⟩ := ht
  have hc' : c < k := hc
  have hq : a * k + c < 5 * k := by nlinarith
  have e1 : (a * k + c) / k = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc', Nat.zero_add]
  have e2 : (a * k + c) % k = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc']
  obtain ⟨h, hw⟩ := hrec _ hq
  rw [e1, e2] at h
  obtain ⟨x, hxK, hxe⟩ := htab.1 _ hw
  have e := mul_eq_of_MULP m.inj (enc_uE1 m (by omega)) (enc_uE1 m (hgK c hc')) hxe
    (enc_uE1 m (by omega)) h
  rw [e, mul_inv_cancel_right, ← hK]
  exact hxK

theorem rec_of {X gK W : ℕ → ℕ} {n k : ℕ}
    (h : (eqK (fun q => R1U (Nat.div q k)) (fun q => R1U (gK (Nat.mod q k))) (fun q => X (W q))
      (fun q => R1U (Nat.div q k)) (5 * k) 1 && ltK W n (5 * k) 1) = true) (hk : 5 * k ≤ 64) :
    ∀ q < 5 * k, MULP (R1U (q / k)) (R1U (gK (q % k))) = MULP (X (W q)) (R1U (q / k)) ∧
      W q < n := by
  simp only [Bool.and_eq_true] at h
  exact fun q hq => ⟨eqK_at h.1 (by omega) q hq, ltK_at h.2 (by omega) q hq⟩

theorem normal_of_le {K : Subgroup G} (hKH : K ≤ g23H m) (hN : g23H m ≤ normalizer (K : Set G)) :
    K ≤ g23H m ∧ (K.subgroupOf (g23H m)).Normal :=
  ⟨hKH, (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hN⟩

theorem K1_le_H : (frameOf m).K₁ ≤ g23H m := by
  rw [g23H]
  exact le_sup_left.trans le_sup_left

theorem K2_le_H : (frameOf m).K₂ ≤ g23H m := by
  rw [g23H]
  exact le_sup_right.trans le_sup_left

theorem K1_normal : (frameOf m).K₁ ≤ g23H m ∧ ((frameOf m).K₁.subgroupOf (g23H m)).Normal := by
  have h := r1_normK
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  refine normal_of_le m (K1_le_H m) (H_le_normalizer m (gK := R1K1G) (W := R1NK1) (n := 24) (k := 2)
    (K1_eq m).symm ?_ ?_ (rec_of (k := 2) (by rw [Bool.and_eq_true]; exact ⟨h1, h2⟩) (by norm_num)))
  · rw [← K1_eq]
    exact (tabK1 m).1
  · intro c hc
    interval_cases c <;> simp [r1KG.1, r1KG.2.1]

theorem K2_normal : (frameOf m).K₂ ≤ g23H m ∧ ((frameOf m).K₂.subgroupOf (g23H m)).Normal := by
  have h := r1_normK
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, h3⟩, h4⟩ := h
  refine normal_of_le m (K2_le_H m) (H_le_normalizer m (gK := R1K2G) (W := R1NK2) (n := 24) (k := 2)
    (K2_eq m).symm ?_ ?_ (rec_of (k := 2) (by rw [Bool.and_eq_true]; exact ⟨h3, h4⟩) (by norm_num)))
  · rw [← K2_eq]
    exact (tabK2 m).1
  · intro c hc
    interval_cases c <;> simp [r1KG.2.2.1, r1KG.2.2.2]

theorem card_Z : Nat.card (frameOf m).Z = 2 := by
  rw [SFrame.Z, Nat.card_zpowers, z_order]

theorem z_mem_K1 : (frameOf m).z ∈ (frameOf m).K₁ := by
  rw [SFrame.z, SFrame.K₁]
  exact pow_mem (subset_closure (by simp)) _

theorem z_mem_K2 : (frameOf m).z ∈ (frameOf m).K₂ := by
  have h := rl' m 32 3 3 11 (by quickRfl)
  rw [uE1_b2, uE1_z] at h
  rw [← h, SFrame.K₂]
  exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem K_inter : (frameOf m).K₁ ⊓ (frameOf m).K₂ = (frameOf m).Z := by
  have hc := cntK_card m.inj (tabK1 m).1 (tabK1 m).2.2 (Gd := fun s => R1U (R1K1G s))
    (g := fun s => uE1 m (R1K1G s)) (k := 2) (hi := 1)
    (fun s hs => enc_uE1 m (by interval_cases s <;> simp [r1KG.1, r1KG.2.1])) (by norm_num)
  rw [Nat.eq_of_beq_eq_true r1_cenK1, K1_eq] at hc
  have hZ : (frameOf m).Z ≤ (frameOf m).K₁ ⊓ (frameOf m).K₂ := by
    rw [SFrame.Z, zpowers_le]
    exact ⟨z_mem_K1 m, z_mem_K2 m⟩
  have hC : (frameOf m).K₁ ⊓ (frameOf m).K₂ ≤
      (frameOf m).K₁ ⊓ centralizer ((fun s => uE1 m (R1K1G s)) '' {s | s < 2}) := by
    intro x hx
    refine ⟨hx.1, mem_centralizer_iff.mpr ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have hy : uE1 m (R1K1G s) ∈ (frameOf m).K₁ := by
      rw [← K1_eq]
      exact subset_closure ⟨s, hs, rfl⟩
    exact K_comm m _ hy x hx.2
  have hZC := Subgroup.eq_of_le_of_card_ge (hZ.trans hC) (by rw [← hc, card_Z])
  exact le_antisymm (hZC ▸ hC) hZ

theorem r1QG : R1Q1G 0 = 5 ∧ R1Q1G 1 = 1 ∧ R1Q2G 0 = 6 ∧ R1Q2G 1 = 3 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem tabQ1 : TabOf m.ρ R1Q1 8 (closure ((fun s => uE1 m (R1Q1G s)) '' {s | s < 2}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1Q1G s)) '' {s | s < 2})) = 8 ∧
    ∀ i < 8, ∀ j < 8, R1Q1 i = R1Q1 j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1Q1G s)) (g := fun s => uE1 m (R1Q1G s)) (by norm_num)
    (fun s hs => enc_uE1 m (by interval_cases s <;> simp [r1QG.1, r1QG.2.1])) r1_ones.2.2.2.2.1
    r1_Q1 (by norm_num) (by norm_num) (by norm_num)

theorem tabQ2 : TabOf m.ρ R1Q2 8 (closure ((fun s => uE1 m (R1Q2G s)) '' {s | s < 2}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1Q2G s)) '' {s | s < 2})) = 8 ∧
    ∀ i < 8, ∀ j < 8, R1Q2 i = R1Q2 j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1Q2G s)) (g := fun s => uE1 m (R1Q2G s)) (by norm_num)
    (fun s hs => enc_uE1 m (by interval_cases s <;> simp [r1QG.2.2.1, r1QG.2.2.2]))
    r1_ones.2.2.2.2.2.1 r1_Q2 (by norm_num) (by norm_num) (by norm_num)

theorem Q1_eq : closure ((fun s => uE1 m (R1Q1G s)) '' {s | s < 2}) =
    closure {(frameOf m).a₁, (frameOf m).b₁} := by
  rw [image2 m r1QG.1 r1QG.2.1, uE1_a1, uE1_b1]

theorem Q2_eq : closure ((fun s => uE1 m (R1Q2G s)) '' {s | s < 2}) =
    closure {(frameOf m).a₂, (frameOf m).b₂} := by
  rw [image2 m r1QG.2.2.1 r1QG.2.2.2, uE1_a2, uE1_b2]

theorem H_norm_Q1 : g23H m ≤ normalizer ((closure {(frameOf m).a₁, (frameOf m).b₁} :
    Subgroup G) : Set G) := by
  have h := r1_normQ
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  refine H_le_normalizer m (gK := R1Q1G) (W := R1NQ1) (n := 8) (k := 2) (Q1_eq m).symm ?_ ?_
    (rec_of (k := 2) (by rw [Bool.and_eq_true]; exact ⟨h1, h2⟩) (by norm_num))
  · rw [← Q1_eq]
    exact (tabQ1 m).1
  · intro c hc
    interval_cases c <;> simp [r1QG.1, r1QG.2.1]

theorem H_norm_Q2 : g23H m ≤ normalizer ((closure {(frameOf m).a₂, (frameOf m).b₂} :
    Subgroup G) : Set G) := by
  have h := r1_normQ
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, h3⟩, h4⟩ := h
  refine H_le_normalizer m (gK := R1Q2G) (W := R1NQ2) (n := 8) (k := 2) (Q2_eq m).symm ?_ ?_
    (rec_of (k := 2) (by rw [Bool.and_eq_true]; exact ⟨h3, h4⟩) (by norm_num))
  · rw [← Q2_eq]
    exact (tabQ2 m).1
  · intro c hc
    interval_cases c <;> simp [r1QG.2.2.1, r1QG.2.2.2]

theorem a1_mem_K1 : (frameOf m).a₁ ∈ (frameOf m).K₁ := by
  have e : (frameOf m).a₁ = (frameOf m).u₁ * (frameOf m).b₁ ^ 3 * (frameOf m).u₁⁻¹ := rfl
  rw [e, SFrame.K₁]
  exact mul_mem (mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _))
    (inv_mem (subset_closure (by simp)))

theorem a2_mem_K2 : (frameOf m).a₂ ∈ (frameOf m).K₂ := by
  have e : (frameOf m).a₂ = (frameOf m).u₂ * (frameOf m).b₂ ^ 3 * (frameOf m).u₂⁻¹ := rfl
  rw [e, SFrame.K₂]
  exact mul_mem (mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _))
    (inv_mem (subset_closure (by simp)))

theorem Q1_le_K1 : closure {(frameOf m).a₁, (frameOf m).b₁} ≤ (frameOf m).K₁ := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact a1_mem_K1 m
  · rw [SFrame.K₁]
    exact subset_closure (by simp)

theorem Q2_le_K2 : closure {(frameOf m).a₂, (frameOf m).b₂} ≤ (frameOf m).K₂ := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact a2_mem_K2 m
  · rw [SFrame.K₂]
    exact subset_closure (by simp)

theorem sylow2_of_card {K Q : Subgroup G} (hQK : Q ≤ K) (hK : Nat.card K = 24)
    (hQ : Nat.card Q = 8) : IsSylowIn 2 K Q := by
  refine ⟨hQK, IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num), ?_⟩
  have h := relIndex_mul_card (H := Q) (K := K)
  rw [inf_of_le_left hQK, hQ, hK] at h
  have h3 : Q.relIndex K = 3 := by omega
  rw [h3]
  norm_num

theorem pCore1 : pCoreOf 2 (frameOf m).K₁ = closure {(frameOf m).a₁, (frameOf m).b₁} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := sylow2_of_card (Q1_le_K1 m) (card_K1 m) (by rw [← Q1_eq]; exact (tabQ1 m).2.1)
  refine pCoreOf_eq_of_sylow hS ((Subgroup.normal_subgroupOf_iff_le_normalizer (Q1_le_K1 m)).mpr ?_)
  exact (K1_le_H m).trans (H_norm_Q1 m)

theorem pCore2 : pCoreOf 2 (frameOf m).K₂ = closure {(frameOf m).a₂, (frameOf m).b₂} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := sylow2_of_card (Q2_le_K2 m) (card_K2 m) (by rw [← Q2_eq]; exact (tabQ2 m).2.1)
  refine pCoreOf_eq_of_sylow hS ((Subgroup.normal_subgroupOf_iff_le_normalizer (Q2_le_K2 m)).mpr ?_)
  exact (K2_le_H m).trans (H_norm_Q2 m)

theorem r1SG : R1SG 0 = 5 ∧ R1SG 1 = 1 ∧ R1SG 2 = 6 ∧ R1SG 3 = 3 ∧ R1SG 4 = 4 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem r1AG : R1AG 0 = 5 ∧ R1AG 1 = 1 ∧ R1AG 2 = 6 ∧ R1AG 3 = 3 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem r1SG_lt : ∀ s < 5, R1SG s < 37 := by
  intro s hs
  obtain ⟨h0, h1, h2, h3, h4⟩ := r1SG
  interval_cases s <;> simp [h0, h1, h2, h3, h4]

theorem r1AG_lt : ∀ s < 4, R1AG s < 37 := by
  intro s hs
  obtain ⟨h0, h1, h2, h3⟩ := r1AG
  interval_cases s <;> simp [h0, h1, h2, h3]

theorem tabS : TabOf m.ρ R1S 64 (closure ((fun s => uE1 m (R1SG s)) '' {s | s < 5}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1SG s)) '' {s | s < 5})) = 64 ∧
    ∀ i < 64, ∀ j < 64, R1S i = R1S j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1SG s)) (g := fun s => uE1 m (R1SG s)) (by norm_num)
    (fun s hs => enc_uE1 m (r1SG_lt s hs)) r1_ones.2.2.2.2.2.2.1 r1_S (by norm_num) (by norm_num)
    (by norm_num)

theorem tabA : TabOf m.ρ R1A 32 (closure ((fun s => uE1 m (R1AG s)) '' {s | s < 4}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1AG s)) '' {s | s < 4})) = 32 ∧
    ∀ i < 32, ∀ j < 32, R1A i = R1A j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1AG s)) (g := fun s => uE1 m (R1AG s)) (by norm_num)
    (fun s hs => enc_uE1 m (r1AG_lt s hs)) r1_ones.2.2.2.2.2.2.2.1 r1_A (by norm_num) (by norm_num)
    (by norm_num)

theorem S_eq : closure ((fun s => uE1 m (R1SG s)) '' {s | s < 5}) = (frameOf m).S := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := r1SG
  have e : (fun s => uE1 m (R1SG s)) '' {s | s < 5} = {(frameOf m).a₁, (frameOf m).b₁,
      (frameOf m).a₂, (frameOf m).b₂, (frameOf m).h₀} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      interval_cases s
      · exact Or.inl (by rw [h0, uE1_a1])
      · exact Or.inr (Or.inl (by rw [h1, uE1_b1]))
      · exact Or.inr (Or.inr (Or.inl (by rw [h2, uE1_a2])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h3, uE1_b2]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [h4, uE1_h0]))))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [h0, uE1_a1]⟩
      · exact ⟨1, by norm_num, by rw [h1, uE1_b1]⟩
      · exact ⟨2, by norm_num, by rw [h2, uE1_a2]⟩
      · exact ⟨3, by norm_num, by rw [h3, uE1_b2]⟩
      · exact ⟨4, by norm_num, by rw [h4, uE1_h0]⟩
  rw [e]
  rfl

theorem A_eq : closure ((fun s => uE1 m (R1AG s)) '' {s | s < 4}) = (frameOf m).A := by
  obtain ⟨h0, h1, h2, h3⟩ := r1AG
  have e : (fun s => uE1 m (R1AG s)) '' {s | s < 4} = {(frameOf m).a₁, (frameOf m).b₁,
      (frameOf m).a₂, (frameOf m).b₂} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      interval_cases s
      · exact Or.inl (by rw [h0, uE1_a1])
      · exact Or.inr (Or.inl (by rw [h1, uE1_b1]))
      · exact Or.inr (Or.inr (Or.inl (by rw [h2, uE1_a2])))
      · exact Or.inr (Or.inr (Or.inr (by rw [h3, uE1_b2])))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [h0, uE1_a1]⟩
      · exact ⟨1, by norm_num, by rw [h1, uE1_b1]⟩
      · exact ⟨2, by norm_num, by rw [h2, uE1_a2]⟩
      · exact ⟨3, by norm_num, by rw [h3, uE1_b2]⟩
  rw [e]
  rfl

theorem S_le_H : (frameOf m).S ≤ g23H m := by
  rw [← S_eq, closure_le]
  rintro x ⟨s, -, rfl⟩
  exact uE1_mem m _

theorem A_le_H : (frameOf m).A ≤ g23H m := by
  rw [← A_eq, closure_le]
  rintro x ⟨s, -, rfl⟩
  exact uE1_mem m _

theorem z_mem_A : (frameOf m).z ∈ (frameOf m).A := by
  rw [SFrame.z, SFrame.A]
  exact pow_mem (subset_closure (by simp)) _

theorem z_mem_S : (frameOf m).z ∈ (frameOf m).S := by
  rw [SFrame.z, SFrame.S]
  exact pow_mem (subset_closure (by simp)) _

theorem cen_eq_Z {X : Subgroup G} {T Gd : ℕ → ℕ} {g : ℕ → G} {n k hi : ℕ}
    (ht : TabOf m.ρ T n (X : Set G)) (hinj : ∀ i < n, ∀ j < n, T i = T j → i = j)
    (hg : ∀ s < k, Enc m.ρ (Gd s) (g s)) (hn : n ≤ 64 * hi) (hX : X = closure (g '' {s | s < k}))
    (hXH : X ≤ g23H m) (hz : (frameOf m).z ∈ X) (hc : cntK T Gd k n hi = 2) :
    cen X = (frameOf m).Z := by
  have h := cntK_card m.inj ht hinj hg hn
  rw [hc] at h
  have e : cen X = X ⊓ centralizer (g '' {s | s < k}) := by
    rw [cen]
    congr 1
    rw [hX, cent_closure]
  have hle : (frameOf m).Z ≤ cen X := by
    rw [SFrame.Z, zpowers_le]
    refine ⟨hz, mem_centralizer_iff.mpr fun y hy => (H_cent_z m y (hXH hy))⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [e, ← h, card_Z]

theorem cen_S : cen (frameOf m).S = (frameOf m).Z := by
  refine cen_eq_Z m (T := R1S) (Gd := fun s => R1U (R1SG s)) (g := fun s => uE1 m (R1SG s))
    (k := 5) (hi := 1) ?_ (tabS m).2.2 (fun s hs => enc_uE1 m (r1SG_lt s hs)) (by norm_num)
    (S_eq m).symm (S_le_H m) (z_mem_S m) (Nat.eq_of_beq_eq_true r1_cenS)
  rw [← S_eq]
  exact (tabS m).1

theorem cen_A : cen (frameOf m).A = (frameOf m).Z := by
  refine cen_eq_Z m (T := R1A) (Gd := fun s => R1U (R1AG s)) (g := fun s => uE1 m (R1AG s))
    (k := 4) (hi := 1) ?_ (tabA m).2.2 (fun s hs => enc_uE1 m (r1AG_lt s hs)) (by norm_num)
    (A_eq m).symm (A_le_H m) (z_mem_A m) (Nat.eq_of_beq_eq_true r1_cenA)
  rw [← A_eq]
  exact (tabA m).1

theorem H_norm_A : g23H m ≤ normalizer ((frameOf m).A : Set G) := by
  have h := r1_normA
  refine H_le_normalizer m (gK := R1AG) (W := R1NA5) (n := 32) (k := 4) (A_eq m).symm ?_ r1AG_lt
    (rec_of (k := 4) h (by norm_num))
  rw [← A_eq]
  exact (tabA m).1

theorem normIn_H_A : normIn (g23H m) (frameOf m).A = g23H m :=
  inf_eq_left.mpr (H_norm_A m)

theorem centIn_H_cen_B : centIn (g23H m) (cen (frameOf m).B) = (frameOf m).B := by
  have h := cntK_card m.inj (tabH' m) (H_inj) (Gd := fun _ => R1U 13) (g := fun _ => uE1 m 13)
    (k := 1) (hi := 9) (fun _ _ => enc_uE1 m (by norm_num)) (by norm_num)
  have e1 : (fun _ => uE1 m 13) '' {s : ℕ | s < 1} = {uE1 m 13} := by
    ext x
    simp [eq_comm]
  rw [e1, Nat.eq_of_beq_eq_true r1_cB, uE1_b1b2] at h
  have e : centIn (g23H m) (cen (frameOf m).B) =
      g23H m ⊓ centralizer ({(frameOf m).b₁ * (frameOf m).b₂} : Set G) := by
    rw [centIn, T5Glue.cen_B m]
    apply le_antisymm
    · exact inf_le_inf_left _
        (centralizer_le (Set.singleton_subset_iff.mpr (subset_closure (by simp))))
    · rintro x ⟨hx, hc⟩
      refine ⟨hx, ?_⟩
      rw [cent_closure]
      refine mem_centralizer_iff.mpr ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact mem_centralizer_iff.mp hc _ rfl
      · exact (H_cent_z m x hx).symm
  have hBH : (frameOf m).B ≤ g23H m := (inf_le_left : (frameOf m).B ≤ (frameOf m).S).trans (S_le_H m)
  have hle : (frameOf m).B ≤ centIn (g23H m) (cen (frameOf m).B) := fun x hx =>
    ⟨hBH hx, mem_centralizer_iff.mpr fun y hy => (mem_centralizer_iff.mp hy.2 x hx).symm⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [e, ← h, T5Glue.card_B m]

theorem r1Y2G : R1Y2G 0 = 16 ∧ R1Y2G 1 = 17 ∧ R1Y2G 2 = 11 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem r1Y3G : R1Y3G 0 = 16 ∧ R1Y3G 1 = 15 ∧ R1Y3G 2 = 11 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem Y2_gens :
    (∀ s < 3, ∀ t < 3, uE1 m (R1Y2G s) * uE1 m (R1Y2G t) = uE1 m (R1Y2G t) * uE1 m (R1Y2G s)) ∧
      ∀ s < 3, uE1 m (R1Y2G s) * uE1 m (R1Y2G s) = 1 :=
  gens3 m (Gd := R1Y2G) r1Y2G.1 r1Y2G.2.1 r1Y2G.2.2
    (by rw [rl' m 50 16 16 7 (by quickRfl), uE1_seven])
    (by rw [rl' m 51 17 17 7 (by quickRfl), uE1_seven])
    (by rw [rl' m 31 11 11 7 (by quickRfl), uE1_seven])
    (rl m 52 16 17 17 16 (by quickRfl)) (rl m 59 16 11 11 16 (by quickRfl))
    (rl m 60 17 11 11 17 (by quickRfl))

theorem Y3_gens :
    (∀ s < 3, ∀ t < 3, uE1 m (R1Y3G s) * uE1 m (R1Y3G t) = uE1 m (R1Y3G t) * uE1 m (R1Y3G s)) ∧
      ∀ s < 3, uE1 m (R1Y3G s) * uE1 m (R1Y3G s) = 1 :=
  gens3 m (Gd := R1Y3G) r1Y3G.1 r1Y3G.2.1 r1Y3G.2.2
    (by rw [rl' m 50 16 16 7 (by quickRfl), uE1_seven])
    (by rw [rl' m 47 15 15 7 (by quickRfl), uE1_seven])
    (by rw [rl' m 31 11 11 7 (by quickRfl), uE1_seven])
    (rl m 53 16 15 15 16 (by quickRfl)) (rl m 59 16 11 11 16 (by quickRfl))
    (rl m 58 15 11 11 15 (by quickRfl))

theorem tabY2 : TabOf m.ρ R1Y2 8 (closure ((fun s => uE1 m (R1Y2G s)) '' {s | s < 3}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1Y2G s)) '' {s | s < 3})) = 8 ∧
    ∀ c < 8, Enc m.ρ (R1Y2 c) (pwG (fun s => uE1 m (R1Y2G s)) 3 c) :=
  basis3 m (lt37 r1Y2G.1 r1Y2G.2.1 r1Y2G.2.2 (by norm_num) (by norm_num) (by norm_num))
    (Y2_gens m).1 (Y2_gens m).2 r1_Y2

theorem tabY3 : TabOf m.ρ R1Y3 8 (closure ((fun s => uE1 m (R1Y3G s)) '' {s | s < 3}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1Y3G s)) '' {s | s < 3})) = 8 ∧
    ∀ c < 8, Enc m.ρ (R1Y3 c) (pwG (fun s => uE1 m (R1Y3G s)) 3 c) :=
  basis3 m (lt37 r1Y3G.1 r1Y3G.2.1 r1Y3G.2.2 (by norm_num) (by norm_num) (by norm_num))
    (Y3_gens m).1 (Y3_gens m).2 r1_Y3

theorem conj_u1 {X Y : Subgroup G} {TX TY gX YW : ℕ → ℕ}
    (htX : ∀ c < 8, Enc m.ρ (TX c) (pwG (fun s => uE1 m (gX s)) 3 c))
    (hX : X = closure ((fun s => uE1 m (gX s)) '' {s | s < 3}))
    (htY : TabOf m.ρ TY 8 ((Y : Subgroup G) : Set G)) (hcard : Nat.card Y ≤ Nat.card X)
    (hrec : ∀ q < 3, MULP (R1U 0) (TX (Nat.shiftLeft 1 q)) = MULP (TY (YW q)) (R1U 0) ∧ YW q < 8) :
    conjSub (frameOf m).u₁ X = Y := by
  refine conjSub_eq_of_gens hX ?_ hcard
  rintro x ⟨q, hq, rfl⟩
  have hq' : q < 3 := hq
  obtain ⟨h, hw⟩ := hrec q hq'
  rw [shl1] at h
  obtain ⟨y, hyY, hye⟩ := htY.1 _ hw
  have hc := htX (2 ^ q) (by interval_cases q <;> norm_num)
  rw [pwG_two_pow hq'] at hc
  have e := mul_eq_of_MULP m.inj (enc_uE1 m (i := 0) (by norm_num)) hc hye
    (enc_uE1 m (i := 0) (by norm_num)) h
  rw [← uE1_u1, e, mul_inv_cancel_right]
  exact hyY

theorem u1_mem_H : (frameOf m).u₁ ∈ g23H m := by
  rw [← uE1_u1]
  exact uE1_mem m 0

theorem Y2_conj : ∃ h ∈ g23H m, closure {(frameOf m).a₁ * (frameOf m).b₂,
    (frameOf m).b₁ * (frameOf m).a₂, (frameOf m).z} = conjSub h (frameOf m).E := by
  have hY : closure ((fun s => uE1 m (R1Y2G s)) '' {s | s < 3}) = closure {(frameOf m).a₁ *
      (frameOf m).b₂, (frameOf m).b₁ * (frameOf m).a₂, (frameOf m).z} := by
    rw [image3 m r1Y2G.1 r1Y2G.2.1 r1Y2G.2.2, uE1_a1b2, uE1_b1a2, uE1_z]
  have h := r1_f19
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  refine ⟨(frameOf m).u₁, u1_mem_H m, (conj_u1 m (tabE m).2.2 (E_eq m).symm (hY ▸ (tabY2 m).1)
    (by rw [← hY, (tabY2 m).2.1, card_E]) fun q hq =>
      ⟨eqK_at h1 (by norm_num) q hq, ltK_at h2 (by norm_num) q hq⟩).symm⟩

theorem Y3_conj : ∃ h ∈ g23H m, closure {(frameOf m).a₁ * (frameOf m).b₂,
    (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂, (frameOf m).z} =
      conjSub h (frameOf m).F := by
  have hY : closure ((fun s => uE1 m (R1Y3G s)) '' {s | s < 3}) = closure {(frameOf m).a₁ *
      (frameOf m).b₂, (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂, (frameOf m).z} := by
    rw [image3 m r1Y3G.1 r1Y3G.2.1 r1Y3G.2.2, uE1_a1b2, uE1_a1b1a2, uE1_z]
  have h := r1_f19
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, h3⟩, h4⟩ := h
  refine ⟨(frameOf m).u₁, u1_mem_H m, (conj_u1 m (tabF m).2.2 (F_eq m).symm (hY ▸ (tabY3 m).1)
    (by rw [← hY, (tabY3 m).2.1, card_F]) fun q hq =>
      ⟨eqK_at h3 (by norm_num) q hq, ltK_at h4 (by norm_num) q hq⟩).symm⟩

theorem p4 : ∀ j < 4, ∀ i < j, ∃ q < 6, R1P4I q = i ∧ R1P4J q = j := by
  intro j hj i hi
  interval_cases j <;> interval_cases i
  · exact ⟨0, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨1, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨3, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨2, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨4, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨5, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem card_normIn_le4 {K : Subgroup G} {TT C D : ℕ → ℕ} {n : ℕ}
    (htab : TabOf m.ρ TT n (K : Set G)) (hC : ∀ i < 4, C i < 576) (hD : ∀ q < 6, D q < 576)
    (heq : ∀ q < 6, MULP (R1H (C (R1P4J q))) (R1H (D q)) = MULP (R1H (C (R1P4I q))) (R1U 7))
    (hw : ∀ q < 6, ∃ g ∈ K, ∃ x, Enc m.ρ x g ∧ ∀ e < n, MULP (R1H (D q)) x ≠ MULP (TT e) (R1H (D q))) :
    4 * Nat.card (normIn (g23H m) K) ≤ 576 := by
  have hch : ∀ i : Fin 4, ∃ g ∈ ((g23H m : Subgroup G) : Set G), Enc m.ρ (R1H (C i)) g :=
    fun i => (tabH' m).1 _ (hC i i.2)
  choose c hcH hce using hch
  have hne : ∀ i j : Fin 4, i.val < j.val → conjSub (c i) K ≠ conjSub (c j) K := by
    intro i j hij
    obtain ⟨q, hq, hqi, hqj⟩ := p4 j.val j.2 i.val hij
    obtain ⟨d, -, hde⟩ := (tabH' m).1 _ (hD q hq)
    have h := heq q hq
    rw [hqi, hqj] at h
    have hd : c j * d = c i * 1 :=
      mul_eq_of_MULP m.inj (hce j) hde (hce i) (r1_ones.1 ▸ enc_one m.ρ) h
    rw [mul_one] at hd
    obtain ⟨g, hgK, x, hx, hwit⟩ := hw q hq
    refine conjSub_ne_of_witness hd hgK fun e' he' => ?_
    obtain ⟨e, he, hee⟩ := htab.2 e' he'
    exact mul_ne_of_MULP hde hx hee hde (hwit e he)
  have h := card_mul_card_normIn_le (T := g23H m) (H := K) c hcH (fun i j hij => by
    by_contra hne'
    rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne' (Fin.ext e)) with hl | hl
    · exact hne i j hl hij
    · exact hne j i hl hij.symm)
  rwa [card_H] at h

theorem card_eq_64 {S N : Subgroup G} (hSN : S ≤ N) (hNH : N ≤ g23H m) (hS : Nat.card S = 64)
    (h4 : 4 * Nat.card N ≤ 576) : Nat.card N = 64 := by
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hSN
  obtain ⟨b, hb⟩ := Subgroup.card_dvd_of_le hNH
  rw [card_H] at hb
  rw [hS] at ha
  rw [ha] at hb h4
  have hb' : 64 * (a * b) = 576 := by rw [← mul_assoc]; exact hb.symm
  have hb9 : a * b = 9 := by omega
  have ha1 : a ≤ 2 := by omega
  interval_cases a <;> omega

theorem card_S : Nat.card (frameOf m).S = 64 := by
  rw [← S_eq]
  exact (tabS m).2.1

theorem tabS' : TabOf m.ρ R1S 64 ((frameOf m).S : Set G) := by
  rw [← S_eq]
  exact (tabS m).1

theorem S_le_normIn_S : (frameOf m).S ≤ normIn (g23H m) (frameOf m).S :=
  fun x hx => ⟨S_le_H m hx, (frameOf m).S.le_normalizer hx⟩

theorem normIn_H_S : normIn (g23H m) (frameOf m).S = (frameOf m).S := by
  have h := r1_conjS
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hle := card_normIn_le4 m (K := (frameOf m).S) (TT := R1S) (C := R1SC) (D := R1SD) (n := 64)
    (tabS' m) (ltK_at h1 (by norm_num)) (ltK_at h2 (by norm_num)) (eqK_at h4 (by norm_num))
    (fun q hq => by
      have hw := ltK_at h3 (by norm_num) q hq
      refine ⟨uE1 m (R1SG (R1SW q)), ?_, _, enc_uE1 m (r1SG_lt _ hw), fun e he => ?_⟩
      · rw [← S_eq]
        exact subset_closure ⟨_, hw, rfl⟩
      · have := neK_at r1_conjSW (by norm_num) (q * 64 + e) (by omega)
        have e1 : Nat.div (q * 64 + e) 64 = q := by change (q * 64 + e) / 64 = q; omega
        have e2 : Nat.mod (q * 64 + e) 64 = e := by change (q * 64 + e) % 64 = e; omega
        rwa [e1, e2] at this)
  have hc := card_eq_64 m (S_le_normIn_S m) inf_le_left (card_S m) hle
  exact (Subgroup.eq_of_le_of_card_ge (S_le_normIn_S m) (by rw [hc, card_S])).symm

theorem r1BG : R1BG 0 = 1 ∧ R1BG 1 = 3 ∧ R1BG 2 = 4 ∧ R1BG 3 = 12 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem r1BG_lt : ∀ s < 4, R1BG s < 37 := by
  intro s hs
  obtain ⟨h0, h1, h2, h3⟩ := r1BG
  interval_cases s <;> simp [h0, h1, h2, h3]

theorem tabB : TabOf m.ρ R1B 32 (closure ((fun s => uE1 m (R1BG s)) '' {s | s < 4}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1BG s)) '' {s | s < 4})) = 32 ∧
    ∀ i < 32, ∀ j < 32, R1B i = R1B j → i = j := by
  have h := r1_B
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, hp⟩, hc⟩, hs⟩ := h
  have hB : (parK R1BPA R1BPB R1BPOS 4 31 1 &&
      closP R1B (fun s => R1U (R1BG s)) R1BPOS 32 4 0 128 2 && sortK R1B R1BSRT R1BSRI 32 1) =
      true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨hp, hc⟩, hs⟩
  exact clos_tab m (X := R1B) (POS := R1BPOS) (PA := R1BPA) (PB := R1BPB) (SRT := R1BSRT)
    (SRI := R1BSRI) (Gd := fun s => R1U (R1BG s)) (g := fun s => uE1 m (R1BG s)) (by norm_num)
    (fun s hs => enc_uE1 m (r1BG_lt s hs)) (Nat.eq_of_beq_eq_true h0) hB (by norm_num) (by norm_num)
    (by norm_num)

attribute [local irreducible] T5Glue.uE T5Glue.gB

theorem B_eq : closure ((fun s => uE1 m (R1BG s)) '' {s | s < 4}) = (frameOf m).B := by
  have g1 : gen5 m 1 = (frameOf m).b₁ := by simp [gen5, sGen_one]
  have g3 : gen5 m 3 = (frameOf m).b₂ := by simp [gen5, sGen_three]
  have e : ∀ s < 4, uE1 m (R1BG s) = T5Glue.gB m s := by
    obtain ⟨h0, h1, h2, h3⟩ := r1BG
    obtain ⟨k0, k1, k2, k3⟩ := T5Glue.q5BG_eq
    intro s hs
    rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [T5Glue.gB, h0, k0, uE1_b1, T5Glue.uE_gen' m 1 (by norm_num), g1]
    · rw [T5Glue.gB, h1, k1, uE1_b2, T5Glue.uE_gen' m 3 (by norm_num), g3]
    · rw [T5Glue.gB, h2, k2, uE1_h0, T5Glue.uE_h0]
    · rw [T5Glue.gB, h3, k3, uE1_a1a2, T5Glue.uE_a1a2]
  rw [← T5Glue.B_eq m]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, (e s hs).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, e s hs⟩

theorem tabB' : TabOf m.ρ R1B 32 ((frameOf m).B : Set G) := by
  rw [← B_eq]
  exact (tabB m).1

theorem S_le_normIn_B : (frameOf m).S ≤ normIn (g23H m) (frameOf m).B := by
  have hBS : (frameOf m).B ≤ (frameOf m).S := inf_le_left
  have hidx : ((frameOf m).B.subgroupOf (frameOf m).S).index = 2 := by
    rw [← Subgroup.relIndex, ← Nat.mul_left_cancel_iff (show 0 < 32 by norm_num)]
    have h := relIndex_mul_card (H := (frameOf m).B) (K := (frameOf m).S)
    rw [inf_of_le_left hBS, T5Glue.card_B m, card_S] at h
    omega
  have hn := Subgroup.normal_of_index_eq_two hidx
  have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mp hn
  exact fun x hx => ⟨S_le_H m hx, hle hx⟩

theorem normIn_H_B : normIn (g23H m) (frameOf m).B = (frameOf m).S := by
  have h := r1_conjB
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hle := card_normIn_le4 m (K := (frameOf m).B) (TT := R1B) (C := R1BC) (D := R1BD) (n := 32)
    (tabB' m) (ltK_at h1 (by norm_num)) (ltK_at h2 (by norm_num)) (eqK_at h4 (by norm_num))
    (fun q hq => by
      have hw := ltK_at h3 (by norm_num) q hq
      refine ⟨uE1 m (R1BG (R1BW q)), ?_, _, enc_uE1 m (r1BG_lt _ hw), fun e he => ?_⟩
      · rw [← B_eq]
        exact subset_closure ⟨_, hw, rfl⟩
      · have := neK_at r1_conjBW (by norm_num) (q * 32 + e) (by omega)
        have e1 : Nat.div (q * 32 + e) 32 = q := by change (q * 32 + e) / 32 = q; omega
        have e2 : Nat.mod (q * 32 + e) 32 = e := by change (q * 32 + e) % 32 = e; omega
        rwa [e1, e2] at this)
  have hc := card_eq_64 m (S_le_normIn_B m) inf_le_left (card_S m) hle
  exact Subgroup.eq_of_le_of_card_ge (S_le_normIn_B m) (by rw [hc, card_S]) |>.symm

theorem r1MG : R1MG 0 = 20 ∧ R1MG 1 = 23 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem r1MG_lt : ∀ s < 2, R1MG s < 37 := by
  intro s hs
  interval_cases s <;> simp [r1MG.1, r1MG.2]

theorem tabM : TabOf m.ρ R1M 192 (closure ((fun s => uE1 m (R1MG s)) '' {s | s < 2}) : Set G) ∧
    Nat.card (closure ((fun s => uE1 m (R1MG s)) '' {s | s < 2})) = 192 ∧
    ∀ i < 192, ∀ j < 192, R1M i = R1M j → i = j :=
  clos_tab m (Gd := fun s => R1U (R1MG s)) (g := fun s => uE1 m (R1MG s)) (by norm_num)
    (fun s hs => enc_uE1 m (r1MG_lt s hs)) r1_ones.2.2.2.2.2.2.2.2.1 r1_M (by norm_num)
    (by norm_num) (by norm_num)

theorem r1EMG : ∀ s < 7, R1EMG s = [20, 23, 5, 1, 6, 3, 19].getD s 0 := by
  intro s hs
  interval_cases s
  all_goals exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem r1EMG_lt : ∀ s < 7, R1EMG s < 37 := by
  intro s hs
  rw [r1EMG s hs]
  interval_cases s <;> simp

theorem tabE' : TabOf m.ρ R1E 8 ((frameOf m).E : Set G) := by
  rw [← E_eq]
  exact (tabE m).1

theorem norm_E {s : ℕ} (hs : s < 7) : uE1 m (R1EMG s) ∈ normalizer ((frameOf m).E : Set G) := by
  have hle : closure ({uE1 m (R1EMG s)} : Set G) ≤ normalizer ((frameOf m).E : Set G) := by
    rw [← E_eq]
    refine closure_le_normalizer ?_
    rintro g hg t ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    have hj' : j < 3 := hj
    have h := actK_at r1_act (by norm_num) s hs j hj'
    have hcol : (R1EM s >>> (3 * j)) &&& 7 < 8 := Nat.lt_succ_of_le Nat.and_le_right
    have hc := (tabE m).2.2 (2 ^ j) (by interval_cases j <;> norm_num)
    rw [pwG_two_pow hj'] at hc
    obtain ⟨y, hy, hye⟩ := (tabE m).1.1 _ hcol
    have e := mul_eq_of_MULP m.inj (enc_uE1 m (r1EMG_lt s hs)) hc hye (enc_uE1 m (r1EMG_lt s hs)) h
    rw [hg, e, mul_inv_cancel_right]
    exact hy
  exact hle (subset_closure rfl)

theorem M_eq_le : closure ((fun s => uE1 m (R1MG s)) '' {s | s < 2}) ≤
    normIn (g23H m) (frameOf m).E := by
  refine le_inf ?_ ?_
  · rw [closure_le]
    rintro x ⟨s, -, rfl⟩
    exact uE1_mem m _
  · rw [closure_le]
    rintro x ⟨s, hs, rfl⟩
    have hs' : s < 2 := hs
    have h := norm_E m (s := s) (by omega)
    rw [r1EMG s (by omega)] at h
    interval_cases s
    · change uE1 m (R1MG 0) ∈ _
      rw [r1MG.1]
      exact h
    · change uE1 m (R1MG 1) ∈ _
      rw [r1MG.2]
      exact h

theorem conjE_ne {ci cj d : ℕ} {q : ℕ} (hq : q < 3) (hi : R1EDI q = ci) (hj : R1EDJ q = cj)
    (hd : R1EDD q = d) (hci : ci < 37) (hcj : cj < 37) (hdd : d < 37) :
    conjSub (uE1 m ci) (frameOf m).E ≠ conjSub (uE1 m cj) (frameOf m).E := by
  have h := r1_conjE
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e := eqK_at h1 (by norm_num) q hq
  rw [hi, hj, hd] at e
  have hd' : uE1 m cj * uE1 m d = uE1 m ci * 1 :=
    mul_eq_of_MULP m.inj (enc_uE1 m hcj) (enc_uE1 m hdd) (enc_uE1 m hci) (r1_ones.1 ▸ enc_one m.ρ) e
  rw [mul_one] at hd'
  have hw := ltK_at h2 (by norm_num) q hq
  have hc := (tabE m).2.2 (2 ^ R1EDW q) (by interval_cases (R1EDW q) <;> norm_num)
  rw [pwG_two_pow hw] at hc
  refine conjSub_ne_of_witness hd' (?_ : uE1 m (R1EG (R1EDW q)) ∈ (frameOf m).E) fun e' he' => ?_
  · rw [← E_eq]
    exact subset_closure ⟨_, hw, rfl⟩
  · obtain ⟨c, hc8, hce⟩ := (tabE' m).2 e' he'
    have hn := neK_at h3 (by norm_num) (q * 8 + c) (by omega)
    have e1 : Nat.div (q * 8 + c) 8 = q := by change (q * 8 + c) / 8 = q; omega
    have e2 : Nat.mod (q * 8 + c) 8 = c := by change (q * 8 + c) % 8 = c; omega
    rw [e1, e2, hd, shl1] at hn
    exact mul_ne_of_MULP (enc_uE1 m hdd) hc hce (enc_uE1 m hdd) hn

theorem card_normIn_H_E : Nat.card (normIn (g23H m) (frameOf m).E) = 192 := by
  let c : Fin 3 → G := fun i => uE1 m ([7, 0, 8].getD i.val 0)
  have hne01 := conjE_ne m (q := 0) (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (ci := 7) (cj := 0) (d := 8) (by norm_num) (by norm_num) (by norm_num)
  have hne02 := conjE_ne m (q := 1) (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (ci := 7) (cj := 8) (d := 0) (by norm_num) (by norm_num) (by norm_num)
  have hne12 := conjE_ne m (q := 2) (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl))
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    (ci := 0) (cj := 8) (d := 8) (by norm_num) (by norm_num) (by norm_num)
  have h3 := card_mul_card_normIn_le (T := g23H m) (H := (frameOf m).E) c (fun i => uE1_mem m _)
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne01
      · exact absurd hij hne02
      · exact absurd hij.symm hne01
      · rfl
      · exact absurd hij hne12
      · exact absurd hij.symm hne02
      · exact absurd hij.symm hne12
      · rfl)
  rw [card_H] at h3
  have hle := Subgroup.card_le_of_le (M_eq_le m)
  rw [(tabM m).2.1] at hle
  omega

theorem M_eq : closure ((fun s => uE1 m (R1MG s)) '' {s | s < 2}) = normIn (g23H m) (frameOf m).E :=
  Subgroup.eq_of_le_of_card_ge (M_eq_le m) (by rw [card_normIn_H_E, (tabM m).2.1])

theorem tabM' : TabOf m.ρ R1M 192 ((normIn (g23H m) (frameOf m).E : Subgroup G) : Set G) := by
  rw [← M_eq]
  exact (tabM m).1

theorem eo_pos : ∀ c < 8, c ≠ 0 → c ≠ 4 → ∃ a < 6, R1EO a = c := by
  intro c hc h0 h4
  interval_cases c
  · exact absurd rfl h0
  · exact ⟨0, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨1, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨2, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact absurd rfl h4
  · exact ⟨3, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨4, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨5, by norm_num, Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem et_idx : ∀ a < 6, ∀ b < 6, R1ETU (6 * a + b) = R1EO a ∧ R1ETV (6 * a + b) = R1EO b := by
  intro a ha b hb
  interval_cases a <;> interval_cases b
  all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem E_pos {u : G} (hu : u ∈ (frameOf m).E) (hz : u ∉ (frameOf m).Z) :
    ∃ a < 6, Enc m.ρ (R1E (R1EO a)) u := by
  obtain ⟨c, hc, hce⟩ := (tabE' m).2 u hu
  have h0 : c ≠ 0 := by
    rintro rfl
    have e1 := (tabE m).2.2 0 (by norm_num)
    have hp : pwG (fun s => uE1 m (R1EG s)) 3 0 = 1 := by
      simp only [pwG, Nat.zero_testBit, Bool.false_eq_true, if_false]
      rfl
    rw [hp] at e1
    exact hz (by rw [enc_unique m.inj hce e1]; exact one_mem _)
  have h4 : c ≠ 4 := by
    rintro rfl
    have e1 := (tabE m).2.2 4 (by norm_num)
    have hp : pwG (fun s => uE1 m (R1EG s)) 3 4 = (frameOf m).z := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pwG_two_pow (by norm_num), r1EG.2.2, uE1_z]
    rw [hp] at e1
    exact hz (by rw [enc_unique m.inj hce e1, SFrame.Z]; exact mem_zpowers _)
  obtain ⟨a, ha, hac⟩ := eo_pos c hc h0 h4
  exact ⟨a, ha, hac ▸ hce⟩

theorem E_trans : ∀ u ∈ (frameOf m).E, u ∉ (frameOf m).Z → ∀ v ∈ (frameOf m).E, v ∉ (frameOf m).Z →
    ∃ k ∈ normIn (g23H m) (frameOf m).E, k * u * k⁻¹ = v := by
  intro u hu huz v hv hvz
  obtain ⟨a, ha, hau⟩ := E_pos m hu huz
  obtain ⟨b, hb, hbv⟩ := E_pos m hv hvz
  have h := r1_transE
  simp only [Bool.and_eq_true] at h
  have hq : 6 * a + b < 36 := by omega
  have e := eqK_at h.1 (by norm_num) _ hq
  have hk := ltK_at h.2 (by norm_num) _ hq
  obtain ⟨hU, hV⟩ := et_idx a ha b hb
  rw [hU, hV] at e
  obtain ⟨k, hkM, hke⟩ := (tabM' m).1 _ hk
  refine ⟨k, hkM, ?_⟩
  rw [mul_eq_of_MULP m.inj hke hau hbv hke e, mul_inv_cancel_right]

theorem fix_E : ∀ e ∈ (frameOf m).E, e ∉ zpowers (frameOf m).z →
    ∃ k ∈ normIn (g23H m) (frameOf m).E, k * e ≠ e * k := by
  intro e he hez
  obtain ⟨a, ha, hae⟩ := E_pos m he hez
  have h := r1_fixE
  simp only [Bool.and_eq_true] at h
  have hn := neK_at h.1 (by norm_num) a ha
  obtain ⟨k, hkM, hke⟩ := (tabM' m).1 _ (ltK_at h.2 (by norm_num) a ha)
  exact ⟨k, hkM, mul_ne_of_MULP hke hae hae hke hn⟩

theorem g23T1_eq : g23T1 m = closure ({(frameOf m).u₁, (frameOf m).b₁, (frameOf m).u₂,
    (frameOf m).b₂, (frameOf m).h₀} ∪ {(frameOf m).σ}) := by
  rw [g23T1]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem sigma_inv : (frameOf m).σ⁻¹ = (frameOf m).σ :=
  (eq_inv_of_mul_eq_one_left (sigma_sq m)).symm

theorem sigma_conj_H {h : G} (hh : h ∈ g23H m) : (frameOf m).σ * h * (frameOf m).σ⁻¹ ∈ g23H m := by
  have hle : closure ({(frameOf m).σ} : Set G) ≤ normalizer ((g23H m : Subgroup G) : Set G) := by
    rw [← H_eq]
    refine closure_le_normalizer ?_
    rintro s hs t ⟨q, hq, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    have hq' : q < 3 := hq
    have hi := idxK_at (Bool.and_eq_true _ _ ▸ r1_genH).2 (by norm_num) q hq'
    have hG : R1HG q < 37 := by
      interval_cases q <;> exact Nat.blt_eq.mp (by quickRfl)
    have he := enc_sig m (enc_uE1 m hG)
    rw [← hi.2] at he
    rw [hs]
    exact mem_of_tabOf m.inj (tabH m) hi.1 he
  exact (mem_normalizer_iff.mp (hle (subset_closure rfl)) h).mp hh

theorem g23H_le_L : g23H m ≤ m.L := by
  rw [g23H_eq, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [frame_u1_mem m, frame_b1_mem m, frame_u2_mem m, frame_b2_mem m, frame_h0_mem m]

theorem sigma_not_mem_H : (frameOf m).σ ∉ g23H m := fun h => m.gS_not_mem (g23H_le_L m h)

theorem H_le_T1 : g23H m ≤ g23T1 m := by
  rw [g23H_eq, g23T1_eq]
  exact closure_mono Set.subset_union_left

theorem sigma_mem_T1 : (frameOf m).σ ∈ g23T1 m := by
  rw [g23T1_eq]
  exact subset_closure (Set.mem_union_right _ rfl)

theorem T1_cases {g : G} (hg : g ∈ g23T1 m) : g ∈ g23H m ∨ g * (frameOf m).σ ∈ g23H m := by
  have hs := sigma_inv m
  have c1 : ∀ h ∈ g23H m, (frameOf m).σ * h * (frameOf m).σ ∈ g23H m := fun h hh => by
    have := sigma_conj_H m hh
    rwa [hs] at this
  rw [g23T1_eq] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inl (by rw [g23H_eq]; exact subset_closure hx)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, sigma_sq]
      exact Or.inr (one_mem _)
  | one => exact Or.inl (one_mem _)
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      have e : x * y * (frameOf m).σ =
          (x * (frameOf m).σ) * ((frameOf m).σ⁻¹ * y * (frameOf m).σ) := by group
      rw [e, hs]
      exact mul_mem hx (c1 y hy)
    · refine Or.inl ?_
      have e : x * y = (x * (frameOf m).σ) * ((frameOf m).σ⁻¹ * (y * (frameOf m).σ) *
          (frameOf m).σ⁻¹) := by group
      rw [e, hs]
      exact mul_mem hx (c1 _ hy)
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have e : x⁻¹ * (frameOf m).σ = (frameOf m).σ * (x * (frameOf m).σ)⁻¹ * (frameOf m).σ := by
        group
      rw [e]
      exact c1 _ (inv_mem hx)

theorem card_T1 : Nat.card (g23T1 m) = 1152 := by
  have hidx : ((g23H m).subgroupOf (g23T1 m)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨(frameOf m).σ, sigma_mem_T1 m⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases T1_cases m b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => sigma_not_mem_H m ?_⟩
      have := mul_mem (inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨hb, fun h => sigma_not_mem_H m ?_⟩
      have := mul_mem (inv_mem h) hb
      rwa [inv_mul_cancel_left] at this
  have h := relIndex_mul_card (H := g23H m) (K := g23T1 m)
  rw [inf_of_le_left (H_le_T1 m), card_H, Subgroup.relIndex, hidx] at h
  omega

theorem T1_le_cent : g23T1 m ≤ centEl ⊤ (frameOf m).z := by
  rw [g23T1_eq, closure_le]
  intro x hx
  refine ⟨trivial, mem_centralizer_singleton_iff.mpr ?_⟩
  rcases hx with hx | hx
  · exact (z_comm_gen m x hx).symm
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have h := sw m 5 11 11 (by quickRfl)
    rw [uE1_z] at h
    exact sigma_comm_of m h

@[expose] noncomputable def pE (c : ℕ) : G := pwG (fun s => uE1 m (R1EG s)) 3 c

theorem pE_mul (c d : ℕ) : pE m c * pE m d = pE m (c ^^^ d) :=
  pwG_mul (E_gens m).1 (E_gens m).2 c d

theorem pE_zero : pE m 0 = 1 := by
  simp only [pE, pwG, Nat.zero_testBit, Bool.false_eq_true, if_false]
  rfl

theorem pE_inv (c : ℕ) : (pE m c)⁻¹ = pE m c := by
  have h := pE_mul m c c
  rw [Nat.xor_self, pE_zero] at h
  exact inv_eq_of_mul_eq_one_right h

theorem pE_z : pE m 4 = (frameOf m).z := by
  rw [pE, show (4 : ℕ) = 2 ^ 2 by norm_num, pwG_two_pow (by norm_num), r1EG.2.2, uE1_z]

theorem enc_pE {c : ℕ} (hc : c < 8) : Enc m.ρ (R1E c) (pE m c) := (tabE m).2.2 c hc

theorem pE_mem {c : ℕ} (hc : c < 8) : pE m c ∈ (frameOf m).E :=
  mem_of_tabOf m.inj (tabE' m) hc (enc_pE m hc)

theorem E_elem {x : G} (hx : x ∈ (frameOf m).E) : ∃ c < 8, x = pE m c := by
  obtain ⟨c, hc, he⟩ := (tabE' m).2 x hx
  exact ⟨c, hc, enc_unique m.inj he (enc_pE m hc)⟩

theorem pE_inj {c d : ℕ} (hc : c < 8) (hd : d < 8) (h : pE m c = pE m d) : c = d := by
  have := enc_inj (enc_pE m hc) (h ▸ enc_pE m hd)
  exact sort_inj (Bool.and_eq_true _ _ ▸ r1_E).2 (by norm_num) c hc d hd this

theorem conjE {s : ℕ} (hs : s < 7) {j : ℕ} (hj : j < 3) :
    uE1 m (R1EMG s) * pE m (2 ^ j) * (uE1 m (R1EMG s))⁻¹ = pE m ((R1EM s >>> (3 * j)) &&& 7) := by
  have h := actK_at r1_act (by norm_num) s hs j hj
  have hcol : (R1EM s >>> (3 * j)) &&& 7 < 8 := Nat.lt_succ_of_le Nat.and_le_right
  have h' := mul_eq_of_MULP m.inj (enc_uE1 m (r1EMG_lt s hs)) (enc_pE m (c := 2 ^ j)
    (by interval_cases j <;> norm_num)) (enc_pE m hcol) (enc_uE1 m (r1EMG_lt s hs)) h
  rw [h', mul_inv_cancel_right]

theorem pE_one_two : pE m 3 = pE m 1 * pE m 2 := by
  rw [pE_mul]
  rfl

theorem conj3E {x : G} {a b : ℕ} (ha : x * pE m 1 * x⁻¹ = pE m a) (hb : x * pE m 2 * x⁻¹ = pE m b) :
    ∀ i : Fin 3, x * pE m (cw i) * x⁻¹ = pE m (![a, b, a ^^^ b] i) := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · change x * pE m 3 * x⁻¹ = pE m (a ^^^ b)
    rw [← pE_mul, ← ha, ← hb, pE_one_two]
    group

theorem Z_elem1 {x : G} (hx : x ∈ (frameOf m).Z) : x = 1 ∨ x = (frameOf m).z := T5Glue.Z_elem m hx

theorem pE_mem_Z_iff {c : ℕ} (hc : c < 8) : pE m c ∈ (frameOf m).Z ↔ c = 0 ∨ c = 4 := by
  constructor
  · intro h
    rcases Z_elem1 m h with h | h
    · rw [← pE_zero m] at h
      exact Or.inl (pE_inj m hc (by norm_num) h)
    · rw [← pE_z m] at h
      exact Or.inr (pE_inj m hc (by norm_num) h)
  · rintro (rfl | rfl)
    · rw [pE_zero]
      exact one_mem _
    · rw [pE_z]
      exact mem_zpowers _

theorem point_ofE {x : G} (i : Fin 3) {c : ℕ} (hc : c < 8) (hxc : x * pE m (cw i) * x⁻¹ = pE m c)
    (j : Fin 3) (hj : (pE m (cw j))⁻¹ * (x * pE m (cw i) * x⁻¹) ∈ (frameOf m).Z) :
    cw j ^^^ c = 0 ∨ cw j ^^^ c = 4 := by
  rw [hxc, pE_inv, pE_mul] at hj
  exact (pE_mem_Z_iff m (xor_lt (cw_lt j) hc)).mp hj

theorem r1EMG_vals : R1EMG 0 = 20 ∧ R1EMG 1 = 23 ∧ R1EMG 2 = 5 ∧ R1EMG 3 = 1 ∧ R1EMG 4 = 6 ∧
    R1EMG 5 = 3 ∧ R1EMG 6 = 19 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem conj01E {s : ℕ} (hs : s < 7) {a b : ℕ}
    (ha : (R1EM s >>> (3 * 0)) &&& 7 = a) (hb : (R1EM s >>> (3 * 1)) &&& 7 = b) :
    uE1 m (R1EMG s) * pE m 1 * (uE1 m (R1EMG s))⁻¹ = pE m a ∧
      uE1 m (R1EMG s) * pE m 2 * (uE1 m (R1EMG s))⁻¹ = pE m b := by
  have h0 := conjE m hs (j := 0) (by norm_num)
  have h1 := conjE m hs (j := 1) (by norm_num)
  rw [ha] at h0
  rw [hb] at h1
  exact ⟨h0, h1⟩

theorem perm_two' : ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ 1 = 2 → σ ^ 2 = 1 ∧ σ ≠ 1 := by decide

theorem card_A : Nat.card (frameOf m).A = 32 := by
  rw [← A_eq]
  exact (tabA m).2.1

theorem A_le_M : (frameOf m).A ≤ normIn (g23H m) (frameOf m).E := by
  rw [← A_eq, closure_le]
  rintro x ⟨s, hs, rfl⟩
  have hs' : s < 4 := hs
  have hgM := idxK_at r1_genM (by norm_num) (s + 1) (by omega)
  have hIMU : R1IMU (s + 1) = R1AG s := by
    obtain ⟨h0, h1, h2, h3⟩ := r1AG
    interval_cases s
    · rw [h0]
      exact Nat.eq_of_beq_eq_true (by quickRfl)
    · rw [h1]
      exact Nat.eq_of_beq_eq_true (by quickRfl)
    · rw [h2]
      exact Nat.eq_of_beq_eq_true (by quickRfl)
    · rw [h3]
      exact Nat.eq_of_beq_eq_true (by quickRfl)
  rw [hIMU] at hgM
  exact mem_of_tabOf m.inj (tabM' m) hgM.1 (by rw [hgM.2]; exact enc_uE1 m (r1AG_lt s hs'))

theorem tau_mem_M : uE1 m 19 ∈ normIn (g23H m) (frameOf m).E := by
  have hgM := idxK_at r1_genM (by norm_num) 0 (by norm_num)
  have h19 : R1IMU 0 = 19 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [h19] at hgM
  exact mem_of_tabOf m.inj (tabM' m) hgM.1 (by rw [hgM.2]; exact enc_uE1 m (by norm_num))

theorem M_le_norm_Z : normIn (g23H m) (frameOf m).E ≤ normalizer ((frameOf m).Z : Set G) := by
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ ?_
  have hgcen : g ∈ Subgroup.centralizer ({(frameOf m).z} : Set G) := H_le_cent_z m hg.1
  simpa only [SFrame.Z, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hgcen

theorem E_S3 : SecProp (normIn (g23H m) (frameOf m).E) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
  set C := normIn (g23H m) (frameOf m).E with hCdef
  let w : Fin 3 → G := fun i => pE m (cw i)
  have hw : ∀ i j : Fin 3, (w j)⁻¹ * w i ∈ (frameOf m).Z → i = j := by
    intro i j h
    have h'' : pE m (cw j ^^^ cw i) ∈ (frameOf m).Z := by
      rw [← pE_mul, ← pE_inv]
      exact h
    have h' := (pE_mem_Z_iff m (xor_lt (cw_lt j) (cw_lt i))).mp h''
    exact (cw_unique (cw i) (cw_lt i) j i h' (Or.inl (Nat.xor_self _))).symm
  have hCZ : C ≤ normalizer ((frameOf m).Z : Set G) := M_le_norm_Z m
  have hP : ∀ x ∈ C, ∀ i, ∃ j, (w j)⁻¹ * (x * w i * x⁻¹) ∈ (frameOf m).Z := by
    intro x hx i
    have hy : x * w i * x⁻¹ ∈ (frameOf m).E :=
      (mem_normalizer_iff.mp hx.2 _).mp (pE_mem m (cw_lt i))
    obtain ⟨c, hc, hyc⟩ := E_elem m hy
    have hc0 : c ≠ 0 ∧ c ≠ 4 := by
      constructor <;> rintro rfl
      · rw [pE_zero] at hyc
        have : w i = 1 := by
          have e : w i = x⁻¹ * (x * w i * x⁻¹) * x := by group
          rw [e, hyc]
          group
        have := pE_inj m (cw_lt i) (by norm_num) (this.trans (pE_zero m).symm)
        fin_cases i <;> simp [cw] at this
      · rw [pE_z] at hyc
        have hz : w i ∈ (frameOf m).Z := by
          have e : w i = x⁻¹ * (x * w i * x⁻¹) * x := by group
          rw [e, hyc]
          have hxi : x⁻¹ ∈ normalizer ((frameOf m).Z : Set G) := inv_mem (hCZ hx)
          have := (mem_normalizer_iff.mp hxi (frameOf m).z).mp (mem_zpowers _)
          simpa using this
        have := (pE_mem_Z_iff m (cw_lt i)).mp hz
        fin_cases i <;> simp [cw] at this
    obtain ⟨j, hj⟩ := cw_exists c hc hc0.1 hc0.2
    refine ⟨j, ?_⟩
    rw [hyc]
    change (pE m (cw j))⁻¹ * pE m c ∈ _
    rw [pE_inv, pE_mul]
    exact (pE_mem_Z_iff m (xor_lt (cw_lt j) hc)).mpr hj
  obtain ⟨φ, hφ⟩ := exists_perm3 w hw hCZ hP
  have hval : ∀ (x : C) (i : Fin 3) {c : ℕ}, c < 8 → (x : G) * pE m (cw i) * (x : G)⁻¹ = pE m c →
      ∀ j : Fin 3, (cw j ^^^ c = 0 ∨ cw j ^^^ c = 4) → φ x i = j := by
    intro x i c hc hxc j hj
    exact cw_unique c hc _ _ (point_ofE m i hc hxc _ (hφ x i)) hj
  have hgC : ∀ s < 2, uE1 m (R1EMG s) ∈ C := by
    intro s hs
    rw [hCdef, ← M_eq]
    refine subset_closure ⟨s, hs, ?_⟩
    interval_cases s
    · change uE1 m (R1MG 0) = uE1 m (R1EMG 0)
      rw [r1MG.1, r1EMG_vals.1]
    · change uE1 m (R1MG 1) = uE1 m (R1EMG 1)
      rw [r1MG.2, r1EMG_vals.2.1]
  have hk3 : orderOf (φ ⟨uE1 m (R1EMG 0), hgC 0 (by norm_num)⟩) = 3 := by
    obtain ⟨ha, hb⟩ := conj01E m (s := 0) (by norm_num) (a := 2) (b := 3)
      (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    have h3 := conj3E m ha hb
    have hσ := perm_three (φ ⟨uE1 m (R1EMG 0), hgC 0 (by norm_num)⟩) (fun i hi => by
      have hz := hφ ⟨_, hgC 0 (by norm_num)⟩ i
      rw [hi] at hz
      fin_cases i
      · exact absurd (point_ofE m 0 (c := 2) (by norm_num) (h3 0) 0 hz) (by decide)
      · exact absurd (point_ofE m 1 (c := 3) (by norm_num) (h3 1) 1 hz) (by decide)
      · exact absurd (point_ofE m 2 (c := 1) (by norm_num) (h3 2) 2 hz) (by decide))
    exact orderOf_eq_prime hσ.1 hσ.2
  have hg2 : orderOf (φ ⟨uE1 m (R1EMG 1), hgC 1 (by norm_num)⟩) = 2 := by
    obtain ⟨ha, hb⟩ := conj01E m (s := 1) (by norm_num) (a := 5) (b := 7)
      (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
    have h3 := conj3E m ha hb
    have h0 := hval ⟨_, hgC 1 (by norm_num)⟩ 0 (by norm_num) (h3 0) 0 (by decide)
    have h1 := hval ⟨_, hgC 1 (by norm_num)⟩ 1 (by norm_num) (h3 1) 2 (by decide)
    have hσ := perm_two' _ h0 h1
    exact orderOf_eq_prime hσ.1 hσ.2
  have hgen : ∀ s, 2 ≤ s → s < 6 → ∀ (h : uE1 m (R1EMG s) ∈ C), φ ⟨_, h⟩ = 1 := by
    intro s hs2 hs6 h
    have key : ∀ a b : ℕ, (R1EM s >>> (3 * 0)) &&& 7 = a → (R1EM s >>> (3 * 1)) &&& 7 = b →
        ∀ i : Fin 3, cw i ^^^ (![a, b, a ^^^ b] i) = 0 ∨ cw i ^^^ (![a, b, a ^^^ b] i) = 4 →
          ![a, b, a ^^^ b] i < 8 → φ ⟨_, h⟩ i = i := by
      intro a b ha hb i hi hlt
      obtain ⟨h0, h1⟩ := conj01E m (by omega) ha hb
      exact hval ⟨_, h⟩ i hlt (conj3E m h0 h1 i) i hi
    ext i
    simp only [Equiv.Perm.coe_one, id_eq]
    interval_cases s
    · exact congrArg Fin.val (key 5 6 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
    · exact congrArg Fin.val (key 1 6 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
    · exact congrArg Fin.val (key 5 2 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
    · exact congrArg Fin.val (key 1 6 (Nat.eq_of_beq_eq_true (by quickRfl))
        (Nat.eq_of_beq_eq_true (by quickRfl)) i (by fin_cases i <;> decide)
        (by fin_cases i <;> decide))
  have hAker : (frameOf m).A ≤ φ.ker.map C.subtype := by
    rw [← A_eq, closure_le]
    rintro x ⟨s, hs, rfl⟩
    have hs' : s < 4 := hs
    have hxC : uE1 m (R1AG s) ∈ C := A_le_M m (by rw [← A_eq]; exact subset_closure ⟨s, hs, rfl⟩)
    refine ⟨⟨uE1 m (R1AG s), hxC⟩, ?_, rfl⟩
    have hEA : R1EMG (s + 2) = R1AG s := by
      obtain ⟨h0, h1, h2, h3⟩ := r1AG
      obtain ⟨-, -, v2, v3, v4, v5, -⟩ := r1EMG_vals
      interval_cases s
      · rw [h0, v2]
      · rw [h1, v3]
      · rw [h2, v4]
      · rw [h3, v5]
    have := hgen (s + 2) (by omega) (by omega) (by rw [hEA]; exact hxC)
    simp only [hEA] at this
    exact this
  have hsurj := perm3_surjective φ hk3 hg2
  refine secProp_perm3 (A_le_M m) φ hsurj (fun x hx => ?_) ?_
  · obtain ⟨y, hy, hyx⟩ := hAker hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rw [card_normIn_H_E, card_A]

theorem tau_cube : uE1 m 19 ^ 3 = 1 := by
  have h33 := rl' m 54 19 19 33 (by quickRfl)
  have h1 := rl' m 55 19 33 7 (by quickRfl)
  rw [uE1_seven] at h1
  rw [pow_succ', pow_two, h33, h1]

theorem tau_order : orderOf (uE1 m 19) = 3 := by
  refine orderOf_eq_prime (tau_cube m) (fun h => ?_)
  have hn := neK_at r1_nrel (by norm_num) 3 (by norm_num)
  have e : R1NA 3 = 19 ∧ R1NB 3 = 7 ∧ R1NC 3 = 7 ∧ R1ND 3 = 7 :=
    ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2] at hn
  have := mul_ne_of_MULP (enc_uE1 m (i := 19) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num))
    (enc_uE1 m (i := 7) (by norm_num)) (enc_uE1 m (i := 7) (by norm_num)) hn
  rw [uE1_seven, mul_one, mul_one, h] at this
  exact this rfl

theorem tau_norm_E : uE1 m 19 ∈ normalizer ((frameOf m).E : Set G) := (tau_mem_M m).2

theorem Z_le_E : (frameOf m).Z ≤ (frameOf m).E := by
  rw [SFrame.Z, zpowers_le, ← pE_z]
  exact pE_mem m (by norm_num)

theorem E_reg : ActsRegularly (zpowers (uE1 m 19)) (frameOf m).E (frameOf m).Z := by
  obtain ⟨ha, hb⟩ := conj01E m (s := 6) (by norm_num) (a := 2) (b := 7)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl))
  rw [r1EMG_vals.2.2.2.2.2.2] at ha hb
  have h3 := conj3E m ha hb 2
  have hT : ∀ i : Fin 4, i ≠ 0 → (![0, 2, 3, 1] : Fin 4 → Fin 4) i ≠ i := by decide
  have hxor : ∀ i j : Fin 4, (j.val ^^^ i.val = 0 ∨ j.val ^^^ i.val = 4) → i = j := by decide
  refine reg_of_cosets (Z_le_E m) (by rw [card_E, card_Z]) (tau_cube m) (tau_norm_E m)
    (M_le_norm_Z m (tau_mem_M m)) (fun i => pE m i.val) (fun i => pE_mem m (by omega))
    (by change pE m 0 ∈ _; rw [pE_zero]; exact one_mem _) (fun i j h => ?_) ![0, 2, 3, 1] hT
    (fun i => ?_)
  · rw [pE_inv, pE_mul] at h
    exact hxor i j ((pE_mem_Z_iff m (xor_lt (by omega) (by omega))).mp h)
  · fin_cases i
    · change (pE m 0)⁻¹ * (uE1 m 19 * pE m 0 * (uE1 m 19)⁻¹) ∈ _
      rw [pE_zero]
      simp only [mul_one, mul_inv_cancel, inv_one]
      exact one_mem _
    · change (pE m 2)⁻¹ * (uE1 m 19 * pE m 1 * (uE1 m 19)⁻¹) ∈ _
      rw [ha, inv_mul_cancel]
      exact one_mem _
    · change (pE m 3)⁻¹ * (uE1 m 19 * pE m 2 * (uE1 m 19)⁻¹) ∈ _
      rw [hb, pE_inv, pE_mul]
      exact (pE_mem_Z_iff m (by decide)).mpr (Or.inr (by decide))
    · change (pE m 1)⁻¹ * (uE1 m 19 * pE m (cw 2) * (uE1 m 19)⁻¹) ∈ _
      rw [h3]
      change (pE m 1)⁻¹ * pE m (2 ^^^ 7) ∈ _
      rw [pE_inv, pE_mul]
      exact (pE_mem_Z_iff m (by decide)).mpr (Or.inr (by decide))

theorem E_le_A : (frameOf m).E ≤ (frameOf m).A := by
  rw [← E_eq, ← A_eq, closure_le]
  rintro x ⟨s, hs, rfl⟩
  have hs' : s < 3 := hs
  obtain ⟨h0, h1, h2, h3⟩ := r1AG
  have hm : ∀ t < 4, uE1 m (R1AG t) ∈ closure ((fun s => uE1 m (R1AG s)) '' {s | s < 4}) :=
    fun t ht => subset_closure ⟨t, ht, rfl⟩
  have ha1 := hm 0 (by norm_num)
  have hb1 := hm 1 (by norm_num)
  have ha2 := hm 2 (by norm_num)
  have hb2 := hm 3 (by norm_num)
  rw [h0] at ha1
  rw [h1] at hb1
  rw [h2] at ha2
  rw [h3] at hb2
  obtain ⟨e0, e1, e2⟩ := r1EG
  interval_cases s
  · change uE1 m (R1EG 0) ∈ _
    rw [e0, ← rl' m 5 1 3 13 (by quickRfl)]
    exact mul_mem hb1 hb2
  · change uE1 m (R1EG 1) ∈ _
    rw [e1, ← rl' m 7 14 6 15 (by quickRfl), ← rl' m 6 5 1 14 (by quickRfl)]
    exact mul_mem (mul_mem ha1 hb1) ha2
  · change uE1 m (R1EG 2) ∈ _
    rw [e2, ← rl' m 3 1 1 11 (by quickRfl)]
    exact mul_mem hb1 hb1

theorem tabA' : TabOf m.ρ R1A 32 ((frameOf m).A : Set G) := by
  rw [← A_eq]
  exact (tabA m).1

theorem A_reg : ActsRegularly (zpowers (uE1 m 19)) (frameOf m).A (frameOf m).E := by
  have hq := r1_cosA
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hW⟩, hT⟩, hZ⟩, hTne⟩, hact1⟩, hact2⟩, hne⟩ := hq
  choose! eA heA using (tabA' m).1
  have hRl : ∀ q : Fin 4, R1RAR q < 32 := fun q => ltK_at hR (by norm_num) q q.2
  have hWl : ∀ q : Fin 4, R1RAW q < 32 := fun q => ltK_at hW (by norm_num) q q.2
  have hTl : ∀ q : Fin 4, R1RAT q < 4 := fun q => ltK_at hT (by norm_num) q q.2
  have hZl : ∀ q : Fin 4, R1RAE q < 8 := fun q => ltK_at hZ (by norm_num) q q.2
  let w : Fin 4 → G := fun q => eA (R1RAR q)
  let T : Fin 4 → Fin 4 := fun q => ⟨R1RAT q, hTl q⟩
  have hR0 : R1RAR 0 = 0 := Nat.eq_of_beq_eq_true (by quickRfl)
  have hw0 : w 0 ∈ (frameOf m).E := by
    have e : w 0 = 1 := by
      have h0 := (heA _ (hRl 0)).2
      rw [show R1RAR ((0 : Fin 4) : ℕ) = 0 from hR0, r1_ones.2.2.2.2.2.2.2.1] at h0
      exact enc_unique m.inj h0 (enc_one m.ρ)
    rw [e]
    exact one_mem _
  have hw : ∀ i j, (w j)⁻¹ * w i ∈ (frameOf m).E → i = j := by
    have key : ∀ i j : Fin 4, i.val < j.val → (w j)⁻¹ * w i ∉ (frameOf m).E := by
      intro i j hij hmem
      obtain ⟨k, hk8, hk⟩ := E_elem m hmem
      have e : w i * 1 = w j * pE m k := by
        rw [mul_one, ← hk]
        group
      have hp4 : ∀ p < 6, R1P4I p = [0, 0, 0, 1, 1, 2].getD p 0 ∧
          R1P4J p = [1, 2, 3, 2, 3, 3].getD p 0 := by
        intro p hp
        interval_cases p
        all_goals exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
      have hp : ∃ p < 6, R1P4I p = i.val ∧ R1P4J p = j.val := by
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
      have hn : MULP (R1A (R1RAR (R1P4I ((8 * p + k) / 8)))) (R1U 7) ≠
          MULP (R1A (R1RAR (R1P4J ((8 * p + k) / 8)))) (R1E ((8 * p + k) % 8)) :=
        neK_at hne (by norm_num) (8 * p + k) (by omega)
      have e1 : (8 * p + k) / 8 = p := by omega
      have e2 : (8 * p + k) % 8 = k := by omega
      rw [e1, e2, hpi, hpj] at hn
      exact mul_ne_of_MULP (heA _ (hRl i)).2 (enc_uE1 m (by norm_num)) (heA _ (hRl j)).2
        (enc_pE m hk8) hn (by rw [uE1_seven]; exact e)
    intro i j h
    by_contra hne'
    rcases lt_or_gt_of_ne (fun e : i.val = j.val => hne' (Fin.ext e)) with hl | hl
    · exact key i j hl h
    · apply key j i hl
      have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  refine reg_of_cosets (E_le_A m) (by rw [card_A, card_E]) (tau_cube m)
    (H_norm_A m (tau_mem_M m).1) (tau_norm_E m) w (fun q => (heA _ (hRl q)).1) hw0 hw T ?_ ?_
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
    have h1 : MULP (R1U 19) (R1A (R1RAR i)) = MULP (R1A (R1RAW i)) (R1U 19) :=
      eqK_at hact1 (by norm_num) i i.2
    have h2 : MULP (R1A (R1RAW i)) (R1U 7) = MULP (R1A (R1RAR (R1RAT i))) (R1E (R1RAE i)) :=
      eqK_at hact2 (by norm_num) i i.2
    obtain ⟨y, -, hy⟩ := (tabA' m).1 _ (hWl i)
    have e1 := mul_eq_of_MULP m.inj (enc_uE1 m (by norm_num)) (heA _ (hRl i)).2 hy
      (enc_uE1 m (by norm_num)) h1
    have e2 := mul_eq_of_MULP m.inj hy (enc_uE1 m (by norm_num)) (heA _ (hRl (T i))).2
      (enc_pE m (hZl i)) h2
    rw [uE1_seven, mul_one] at e2
    have e3 : uE1 m 19 * w i * (uE1 m 19)⁻¹ = y := by
      change uE1 m 19 * eA (R1RAR i) * (uE1 m 19)⁻¹ = y
      rw [e1, mul_inv_cancel_right]
    rw [e3, e2]
    change (eA (R1RAR (R1RAT i)))⁻¹ * (eA (R1RAR (R1RAT i)) * pE m (R1RAE i)) ∈ _
    rw [inv_mul_cancel_left]
    exact pE_mem m (hZl i)

theorem E_sylow : ∀ T : Subgroup G, IsSylowIn 3 (normIn (g23H m) (frameOf m).E) T →
    ActsRegularly T (frameOf m).E (frameOf m).Z ∧ ActsRegularly T (frameOf m).A (frameOf m).E := by
  have h0 : IsSylowIn 3 (normIn (g23H m) (frameOf m).E) (zpowers (uE1 m 19)) :=
    sylow3 (tau_mem_M m) (tau_order m) (n := 64) (by rw [card_normIn_H_E]) (by norm_num)
  refine forall_isSylowIn_of_one h0 ⟨E_reg m, A_reg m⟩ (fun g hg h => ⟨?_, ?_⟩)
  · exact actsRegularly_conj hg.2 (M_le_norm_Z m hg) h.1
  · exact actsRegularly_conj (H_norm_A m hg.1) hg.2 h.2

theorem z_central_T1 {g : G} (hg : g ∈ g23T1 m) : g * (frameOf m).z = (frameOf m).z * g :=
  mem_centralizer_singleton_iff.mp (T1_le_cent m hg).2

theorem comm_cases {y g : G} (hy : y ∈ g23T1 m) (hg : g ∈ g23T1 m) (h : ⁅y, g⁆ ∈ (frameOf m).Z) :
    g * y = y * g ∨ g * y = y * (frameOf m).z * g := by
  have hzy : y * (frameOf m).z = (frameOf m).z * y := z_central_T1 m hy
  rw [commutatorElement_def] at h
  rcases Z_elem1 m h with h | h
  · left
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  · right
    rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul] at h
    calc g * y = (frameOf m).z * (frameOf m).z * (g * y) := by rw [z_sq, one_mul]
      _ = (frameOf m).z * ((frameOf m).z * g * y) := by group
      _ = (frameOf m).z * (y * g) := by rw [← h]
      _ = y * (frameOf m).z * g := by
        rw [hzy]
        group

theorem commMod_eq {X : Subgroup G} {gX C : ℕ → ℕ} {k : ℕ}
    (hgen : ∀ s < k, uE1 m (gX s) ∈ X) (hXH : X ≤ g23H m)
    (hgX : ∀ s < k, gX s < 37) (hC : ∀ s < k, C s < 37 ∧ uE1 m (C s) = uE1 m (gX s) * (frameOf m).z)
    (hAS : ∀ a ∈ (frameOf m).A, ∀ y ∈ X, ⁅y, a⁆ ∈ (frameOf m).Z)
    (hcnt : cntMK R1H (fun s => R1U (gX s)) (fun s => R1U (gX s)) (fun s => R1U (C s)) k 576 9 = 32)
    (hcnt0 : cntMK R1H (fun s => SWP (R1U (gX s))) (fun s => R1U (gX s)) (fun s => R1U (C s)) k 576 9
      = 0) :
    {g : G | g ∈ g23T1 m ∧ ∀ y ∈ X, ⁅y, g⁆ ∈ (frameOf m).Z} = ((frameOf m).A : Set G) := by
  classical
  have : Fintype (frameOf m).A := Fintype.ofFinite _
  have hXT : ∀ y ∈ X, y ∈ g23T1 m := fun y hy => H_le_T1 m (hXH hy)
  let P : ℕ → Prop := fun i => ∀ s < k, MULP (R1H i) (R1U (gX s)) = MULP (R1U (gX s)) (R1H i) ∨
    MULP (R1H i) (R1U (gX s)) = MULP (R1U (C s)) (R1H i)
  have hFs : ((Finset.range 576).filter P).card = 32 := by
    rw [← hcnt, cntMK_spec _ _ _ _ (by norm_num)]
  have hPi : ∀ g ∈ g23H m, (∀ y ∈ X, ⁅y, g⁆ ∈ (frameOf m).Z) → ∀ i < 576, Enc m.ρ (R1H i) g → P i := by
    intro g hgH hg i hi he s hs
    rcases comm_cases m (hXT _ (hgen s hs)) (H_le_T1 m hgH) (hg _ (hgen s hs)) with e | e
    · exact Or.inl (enc_inj (enc_mul m.ρ he (enc_uE1 m (hgX s hs)))
        (e ▸ enc_mul m.ρ (enc_uE1 m (hgX s hs)) he))
    · refine Or.inr (enc_inj (enc_mul m.ρ he (enc_uE1 m (hgX s hs))) ?_)
      rw [e, ← (hC s hs).2]
      exact enc_mul m.ρ (enc_uE1 m (hC s hs).1) he
  have hnoσ : ∀ g ∈ g23T1 m, (∀ y ∈ X, ⁅y, g⁆ ∈ (frameOf m).Z) → g ∈ g23H m := by
    intro g hgT hg
    rcases T1_cases m hgT with h | h
    · exact h
    exfalso
    obtain ⟨i, hi, he⟩ := (tabH' m).2 _ h
    have hP' : ∀ s < k, MULP (R1H i) (SWP (R1U (gX s))) = MULP (R1U (gX s)) (R1H i) ∨
        MULP (R1H i) (SWP (R1U (gX s))) = MULP (R1U (C s)) (R1H i) := by
      intro s hs
      have hsw := enc_sig m (enc_uE1 m (hgX s hs))
      have hσ : g = g * (frameOf m).σ * (frameOf m).σ := by rw [mul_assoc, sigma_sq, mul_one]
      have key : g * (frameOf m).σ * ((frameOf m).σ * uE1 m (gX s) * (frameOf m).σ⁻¹) =
          g * uE1 m (gX s) * (frameOf m).σ := by
        rw [sigma_inv]
        simp only [mul_assoc]
        rw [← mul_assoc (frameOf m).σ (frameOf m).σ, sigma_sq, one_mul]
      rcases comm_cases m (hXT _ (hgen s hs)) hgT (hg _ (hgen s hs)) with e | e
      · refine Or.inl (enc_inj (enc_mul m.ρ he hsw) ?_)
        rw [key, e, mul_assoc]
        exact enc_mul m.ρ (enc_uE1 m (hgX s hs)) he
      · refine Or.inr (enc_inj (enc_mul m.ρ he hsw) ?_)
        rw [key, e, ← (hC s hs).2, mul_assoc]
        exact enc_mul m.ρ (enc_uE1 m (hC s hs).1) he
    have hmem : i ∈ (Finset.range 576).filter fun i => ∀ s < k,
        MULP (R1H i) (SWP (R1U (gX s))) = MULP (R1U (gX s)) (R1H i) ∨
          MULP (R1H i) (SWP (R1U (gX s))) = MULP (R1U (C s)) (R1H i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hP'⟩
    have h0 := hcnt0
    rw [cntMK_spec _ _ _ _ (by norm_num)] at h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  have hidx : ∀ a : (frameOf m).A, ∃ i < 576, Enc m.ρ (R1H i) a :=
    fun a => (tabH' m).2 _ (A_le_H m a.2)
  choose ia hia hiae using hidx
  have hinj : Function.Injective ia := fun a b h => Subtype.ext
    (enc_unique m.inj (hiae a) (h ▸ hiae b))
  have himg : Finset.univ.image ia = (Finset.range 576).filter P := by
    refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hia a),
        hPi a (A_le_H m a.2) (hAS a a.2) _ (hia a) (hiae a)⟩
    · rw [hFs, Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
        card_A]
  ext g
  constructor
  · rintro ⟨hgT, hg⟩
    have hgH := hnoσ g hgT hg
    obtain ⟨i, hi, he⟩ := (tabH' m).2 _ hgH
    have hiP : i ∈ (Finset.range 576).filter P :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hPi g hgH hg i hi he⟩
    rw [← himg] at hiP
    obtain ⟨a, -, hai⟩ := Finset.mem_image.mp hiP
    have : (a : G) = g := enc_unique m.inj (hiae a) (hai ▸ he)
    rw [← this]
    exact a.2
  · intro hg
    exact ⟨H_le_T1 m (A_le_H m hg), hAS g hg⟩

theorem z_mem_Z : (frameOf m).z ∈ (frameOf m).Z := mem_zpowers _

theorem comm_mul_left {a a' b : G} (ha : a ∈ g23T1 m) (h : ⁅a, b⁆ ∈ (frameOf m).Z)
    (h' : ⁅a', b⁆ ∈ (frameOf m).Z) : ⁅a * a', b⁆ ∈ (frameOf m).Z := by
  have e : ⁅a * a', b⁆ = (a * ⁅a', b⁆ * a⁻¹) * ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    group
  have hc : a * ⁅a', b⁆ * a⁻¹ = ⁅a', b⁆ := by
    rcases Z_elem1 m h' with e1 | e1
    · rw [e1, mul_one, mul_inv_cancel]
    · rw [e1, z_central_T1 m ha, mul_inv_cancel_right]
  rw [e, hc]
  exact mul_mem h' h

theorem comm_inv_left {a b : G} (ha : a ∈ g23T1 m) (h : ⁅a, b⁆ ∈ (frameOf m).Z) :
    ⁅a⁻¹, b⁆ ∈ (frameOf m).Z := by
  have e : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a := by
    simp only [commutatorElement_def]
    group
  rw [e]
  rcases Z_elem1 m (inv_mem h) with e1 | e1
  · rw [e1, mul_one, inv_mul_cancel]
    exact one_mem _
  · rw [e1]
    have hz := z_central_T1 m ha
    have : a⁻¹ * (frameOf m).z * a = (frameOf m).z := by
      rw [mul_assoc, ← hz, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact z_mem_Z m

theorem comm_symm {a b : G} (h : ⁅a, b⁆ ∈ (frameOf m).Z) : ⁅b, a⁆ ∈ (frameOf m).Z := by
  have e : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact inv_mem h

theorem comm_mod_A : ∀ a ∈ (frameOf m).A, ∀ b ∈ (frameOf m).A, ⁅a, b⁆ ∈ (frameOf m).Z := by
  have hAT : ∀ x ∈ (frameOf m).A, x ∈ g23T1 m := fun x hx => H_le_T1 m (A_le_H m hx)
  have hgens : ∀ s < 4, ∀ t < 4, ⁅uE1 m (R1AG s), uE1 m (R1AG t)⁆ ∈ (frameOf m).Z := by
    have c1 : ∀ x y : G, x * y = y * x → ⁅x, y⁆ ∈ (frameOf m).Z := fun x y h => by
      have e : ⁅x, y⁆ = 1 := by
        rw [commutatorElement_def, h]
        group
      rw [e]
      exact one_mem _
    have c2 : ∀ x y : G, x ∈ g23T1 m → y ∈ g23T1 m → x * y = y * (x * (frameOf m).z) →
        ⁅x, y⁆ ∈ (frameOf m).Z := fun x y hx hy h => by
      have hzx := z_central_T1 m hx
      have hzy := z_central_T1 m hy
      have e : ⁅x, y⁆ = (frameOf m).z := by
        calc ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
          _ = y * (x * (frameOf m).z) * x⁻¹ * y⁻¹ := by rw [h]
          _ = y * ((frameOf m).z * x) * x⁻¹ * y⁻¹ := by rw [hzx]
          _ = y * (frameOf m).z * y⁻¹ := by group
          _ = (frameOf m).z * y * y⁻¹ := by rw [hzy]
          _ = (frameOf m).z := by group
      rw [e]
      exact z_mem_Z m
    have hyT : ∀ t < 4, uE1 m (R1AG t) ∈ g23T1 m := fun t ht => H_le_T1 m (uE1_mem m _)
    have z25 := rl' m 17 5 11 25 (by quickRfl)
    have z27 := rl' m 19 6 11 27 (by quickRfl)
    have r61 := rl m 61 5 1 1 25 (by quickRfl)
    have r62 := rl m 62 5 6 6 5 (by quickRfl)
    have r63 := rl m 63 5 3 3 5 (by quickRfl)
    have r64 := rl m 64 1 6 6 1 (by quickRfl)
    have r65 := rl m 65 1 3 3 1 (by quickRfl)
    have r66 := rl m 66 6 3 3 27 (by quickRfl)
    rw [← z25, uE1_z] at r61
    rw [← z27, uE1_z] at r66
    obtain ⟨h0, h1, h2, h3⟩ := r1AG
    have refl : ∀ x : G, ⁅x, x⁆ ∈ (frameOf m).Z := fun x => c1 x x rfl
    intro s hs t ht
    interval_cases s <;> interval_cases t <;> simp only [h0, h1, h2, h3]
    · exact refl _
    · exact c2 _ _ (by rw [← h0]; exact hyT 0 (by norm_num))
        (by rw [← h1]; exact hyT 1 (by norm_num)) r61
    · exact c1 _ _ r62
    · exact c1 _ _ r63
    · exact comm_symm m (c2 _ _ (by rw [← h0]; exact hyT 0 (by norm_num))
        (by rw [← h1]; exact hyT 1 (by norm_num)) r61)
    · exact refl _
    · exact c1 _ _ r64
    · exact c1 _ _ r65
    · exact comm_symm m (c1 _ _ r62)
    · exact comm_symm m (c1 _ _ r64)
    · exact refl _
    · exact c2 _ _ (by rw [← h2]; exact hyT 2 (by norm_num))
        (by rw [← h3]; exact hyT 3 (by norm_num)) r66
    · exact comm_symm m (c1 _ _ r63)
    · exact comm_symm m (c1 _ _ r65)
    · exact comm_symm m (c2 _ _ (by rw [← h2]; exact hyT 2 (by norm_num))
        (by rw [← h3]; exact hyT 3 (by norm_num)) r66)
    · exact refl _
  have hstep : ∀ b ∈ (frameOf m).A, (∀ t < 4, ⁅uE1 m (R1AG t), b⁆ ∈ (frameOf m).Z) →
      ∀ a ∈ (frameOf m).A, ⁅a, b⁆ ∈ (frameOf m).Z := by
    intro b hb hbg a ha
    rw [← A_eq] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact hbg t ht
    | one =>
      simp only [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      exact comm_mul_left m (hAT x (by rw [← A_eq]; exact hx)) ihx ihy
    | inv x hx ihx => exact comm_inv_left m (hAT x (by rw [← A_eq]; exact hx)) ihx
  intro a ha b hb
  refine hstep b hb (fun t ht => ?_) a ha
  refine comm_symm m (hstep _ (by rw [← A_eq]; exact subset_closure ⟨t, ht, rfl⟩) (fun s hs => ?_) b hb)
  exact comm_symm m (hgens t ht s hs)

theorem z_gen {a c : ℕ} (h : uE1 m a * uE1 m 11 = uE1 m c) : uE1 m c = uE1 m a * (frameOf m).z := by
  rw [← h, uE1_z]

theorem commMod_A : {g : G | g ∈ g23T1 m ∧ ∀ a ∈ (frameOf m).A, ⁅a, g⁆ ∈ (frameOf m).Z} =
    ((frameOf m).A : Set G) := by
  obtain ⟨h0, h1, h2, h3⟩ := r1AG
  refine commMod_eq m (gX := R1AG) (C := fun s => Nat.add 25 s) (k := 4)
    (fun s hs => by rw [← A_eq]; exact subset_closure ⟨s, hs, rfl⟩) (A_le_H m) r1AG_lt
    (fun s hs => ⟨by change 25 + s < 37; omega, ?_⟩) (fun a ha y hy => comm_mod_A m y hy a ha)
    (Nat.eq_of_beq_eq_true r1_cmA) (Nat.eq_of_beq_eq_true r1_cmAs)
  interval_cases s
  · rw [h0]
    exact z_gen m (rl' m 17 5 11 25 (by quickRfl))
  · rw [h1]
    exact z_gen m (rl' m 18 1 11 26 (by quickRfl))
  · rw [h2]
    exact z_gen m (rl' m 19 6 11 27 (by quickRfl))
  · rw [h3]
    exact z_gen m (rl' m 20 3 11 28 (by quickRfl))

theorem r1EFG : R1EFG 0 = 12 ∧ R1EFG 1 = 13 ∧ R1EFG 2 = 15 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem F_le_A : (frameOf m).F ≤ (frameOf m).A := by
  rw [← F_eq, closure_le]
  rintro x ⟨s, hs, rfl⟩
  have hs' : s < 3 := hs
  obtain ⟨f0, f1, f2⟩ := r1FG
  have hE : ∀ c, c = 13 ∨ c = 11 → uE1 m c ∈ (frameOf m).A := by
    rintro c (rfl | rfl)
    · exact E_le_A m (by rw [← E_eq]; exact subset_closure ⟨0, by norm_num, by simp only [r1EG.1]⟩)
    · exact E_le_A m (by rw [← E_eq]; exact subset_closure ⟨2, by norm_num, by simp only [r1EG.2.2]⟩)
  interval_cases s
  · change uE1 m (R1FG 0) ∈ _
    rw [f0, uE1_a1a2, SFrame.A]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · change uE1 m (R1FG 1) ∈ _
    rw [f1]
    exact hE 13 (Or.inl rfl)
  · change uE1 m (R1FG 2) ∈ _
    rw [f2]
    exact hE 11 (Or.inr rfl)

theorem EF_le_A : (frameOf m).E ⊔ (frameOf m).F ≤ (frameOf m).A := sup_le (E_le_A m) (F_le_A m)

theorem commMod_EF : {g : G | g ∈ g23T1 m ∧ ∀ y ∈ (frameOf m).E ⊔ (frameOf m).F,
    ⁅y, g⁆ ∈ (frameOf m).Z} = ((frameOf m).A : Set G) := by
  obtain ⟨e0, e1, e2⟩ := r1EFG
  have hgen : ∀ s < 3, uE1 m (R1EFG s) ∈ (frameOf m).E ⊔ (frameOf m).F := by
    intro s hs
    interval_cases s
    · rw [e0]
      exact mem_sup_right (by rw [← F_eq]; exact subset_closure ⟨0, by norm_num, by simp only [r1FG.1]⟩)
    · rw [e1]
      exact mem_sup_right (by rw [← F_eq]; exact subset_closure ⟨1, by norm_num, by simp only [r1FG.2.1]⟩)
    · rw [e2]
      exact mem_sup_left (by rw [← E_eq]; exact subset_closure ⟨1, by norm_num, by simp only [r1EG.2.1]⟩)
  refine commMod_eq m (gX := R1EFG) (C := fun s => Nat.add 29 s) (k := 3) hgen
    ((EF_le_A m).trans (A_le_H m)) (fun s hs => by interval_cases s <;> simp [e0, e1, e2])
    (fun s hs => ⟨by change 29 + s < 37; omega, ?_⟩)
    (fun a ha y hy => comm_mod_A m y (EF_le_A m hy) a ha)
    (Nat.eq_of_beq_eq_true r1_cmEF) (Nat.eq_of_beq_eq_true r1_cmEFs)
  interval_cases s
  · rw [e0]
    exact z_gen m (rl' m 21 12 11 29 (by quickRfl))
  · rw [e1]
    exact z_gen m (rl' m 22 13 11 30 (by quickRfl))
  · rw [e2]
    exact z_gen m (rl' m 23 15 11 31 (by quickRfl))

end CFSG.KD.G2Three.Sec1.T1Glue

end
