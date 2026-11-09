
module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsBase

public section

namespace CertificateChecks.KernelLC

open Equiv MulAction CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu
open CFSG.Monster.B.Classical.Plane
open scoped Pointwise

theorem hexadList_checks' : hexadList.length = 77 ∧ hexadList.Nodup ∧ hexad0 ∈ hexadList ∧
    hexadList.all (fun B => B.card == 6) = true ∧
    hexadList.all (fun B => hexadMasks.contains (mask (B.map m22gA.toEmbedding)) &&
      hexadMasks.contains (mask (B.map m22gB.toEmbedding))) = true := by
  decide +kernel

@[expose] def hexadMaskLits : List ℕ :=
  [655879, 1065035, 270387, 2163075, 39939, 12429, 3147797, 33125, 345093, 132377, 68137, 2916361,
    594001, 49809, 1574049, 2248737, 395457, 2106945, 1315585, 551169, 1286145, 2098222, 20758,
    75846, 1343622, 526490, 41738, 462858, 2261074, 1115666, 4834, 1181986, 639010, 787778, 156802,
    2378242, 3682306, 262748, 1638668, 182284, 196788, 566292, 1073700, 792612, 2638020, 1184836,
    3972, 2498820, 2200068, 1085496, 2187288, 663656, 278952, 99528, 2103624, 3277448, 546312,
    1321992, 19568, 2622256, 1057232, 2364560, 362768, 145936, 1982480, 3473504, 2140320, 79136,
    427552, 213824, 1608256, 323648, 692608, 860800, 1136768, 3196160, 2821120]

theorem hexadMasks_eq_lits : hexadMasks = hexadMaskLits := by
  decide +kernel

@[expose] def tripleCount (L : List ℕ) (a b c : ℕ) : ℕ :=
  (L.filter fun m => m.testBit a && m.testBit b && m.testBit c).length

@[expose] def triplesB (L : List ℕ) : Bool :=
  (List.range 22).all fun c => (List.range c).all fun b => (List.range b).all fun a =>
    tripleCount L a b c == 1

theorem triplesB_lits : triplesB hexadMaskLits = true := by
  decide +kernel

theorem tripleCount_swap12 (L : List ℕ) (a b c : ℕ) :
    tripleCount L a b c = tripleCount L b a c := by
  unfold tripleCount
  congr 2
  funext m
  cases m.testBit a <;> cases m.testBit b <;> rfl

theorem tripleCount_swap23 (L : List ℕ) (a b c : ℕ) :
    tripleCount L a b c = tripleCount L a c b := by
  unfold tripleCount
  congr 2
  funext m
  cases m.testBit a <;> cases m.testBit b <;> cases m.testBit c <;> rfl

theorem tripleCount_of_triplesB {L : List ℕ} (h : triplesB L = true) {a b c : ℕ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : a < 22) (hb : b < 22) (hc : c < 22) :
    tripleCount L a b c = 1 := by
  have key : ∀ a b c, a < b → b < c → c < 22 → tripleCount L a b c = 1 := by
    intro a b c h1 h2 h3
    simp only [triplesB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact h c h3 b h2 a h1
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3 <;>
    first
    | exact key _ _ _ (by omega) (by omega) (by omega)
    | (rw [tripleCount_swap12]; exact key _ _ _ (by omega) (by omega) (by omega))
    | (rw [tripleCount_swap23]; exact key _ _ _ (by omega) (by omega) (by omega))
    | (rw [tripleCount_swap12, tripleCount_swap23]
       exact key _ _ _ (by omega) (by omega) (by omega))
    | (rw [tripleCount_swap23, tripleCount_swap12]
       exact key _ _ _ (by omega) (by omega) (by omega))
    | (rw [tripleCount_swap12, tripleCount_swap23, tripleCount_swap12]
       exact key _ _ _ (by omega) (by omega) (by omega))

theorem hexadMasks_triples' : ∀ x y z : Fin 22, x ≠ y → x ≠ z → y ≠ z →
    (hexadMasks.filter fun m => m.testBit x && m.testBit y && m.testBit z).length = 1 := by
  intro x y z hxy hxz hyz
  rw [hexadMasks_eq_lits]
  exact tripleCount_of_triplesB triplesB_lits (Fin.val_ne_of_ne hxy) (Fin.val_ne_of_ne hxz)
    (Fin.val_ne_of_ne hyz) x.2 y.2 z.2

theorem hexadMasks_intersections' : ∀ m ∈ hexadMasks,
    (hexadMasks.filter fun m' => interBits m m' == 0).length = 16 ∧
      (hexadMasks.filter fun m' => interBits m m' == 2).length = 60 := by
  rw [hexadMasks_eq_lits]
  decide +kernel

@[expose] def wordPerm (w : List Bool) : Perm (Fin 22) :=
  w.foldr (fun b g => (if b then m22gB else m22gA) * g) 1

theorem wordPerm_mem (w : List Bool) : wordPerm w ∈ M22 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    rw [M22, m22_eq]
    cases b
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def hexWords : List (List Bool) :=
  [[],
    [true, true, false, true, false, true, true, true, false, true],
    [false, true, false, true, true, false, true],
    [false, true, false, true, true, false, true, false],
    [false, true, true],
    [true, true],
    [false, true, true, true, false, true, true],
    [true, false, true, true, true, false, true, true, true],
    [false, true, false, true, true, false, true, true, false, true],
    [true, false, true],
    [false, true, true, false, true],
    [false, true, true, true, false, true, false, true, false],
    [true, true, false, true, false, true, true],
    [false, true, true, true, false, true],
    [false, true, true, true],
    [true, true, true, false, true, false, true, true, true, false, true],
    [true, false, true, false, true, false],
    [true, false, true, true, true],
    [true, true, true, false, true, false, true, true, false, true, false],
    [true, true, false, true, false],
    [false, true, false, true, false, true, true, true, false, true],
    [false, true, false, true, true, true, false, true],
    [true, true, true, false, true],
    [true, true, false, true, true, false, true],
    [true, true, false, true, true, true, false, true, false, true, false],
    [true, false, true, false, true],
    [true, false],
    [false, true, false, true, false, true, false],
    [true, false, true, true],
    [false, true, false, true, false],
    [true, false, true, true, false, true, false],
    [false, true],
    [false, true, true, false, true, true, true],
    [true, false, true, false, true, true, true],
    [true, true, false, true, true, false, true, false],
    [true, true, true, false, true, false, true, true],
    [true, true, true],
    [true, true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, true, false, true, false],
    [true, true, false, true, true],
    [false, true, false, true, true],
    [true, true, false, true, true, true, false, true],
    [true, true, true, false, true, true, true],
    [true, true, true, false, true, false, true, false],
    [true, true, false, true, true, true],
    [true, false, true, false, true, true, true, false, true],
    [false, true, false],
    [true, false, true, false, true, true, false, true, false],
    [true, false, true, true, true, false, true, false, true, false],
    [true, true, true, false, true, true],
    [true, true, false, true, false, true, false],
    [true, true, true, false, true, true, false, true, false],
    [false, true, true, true, false, true, false, true, true],
    [false, true, true, false, true, true, false, true],
    [true, true, false, true],
    [true],
    [false, true, true, false, true, false],
    [true, false, true, false, true, true],
    [false, true, true, false, true, false, true, false],
    [true, true, true, false, true, false],
    [true, false, true, false],
    [true, false, true, true, false, true],
    [false, true, true, false, true, false, true, true, false, true],
    [false, true, false, true],
    [true, true, true, false, true, true, false, true],
    [true, false, true, false, true, true, false, true, true, false, true],
    [true, false, true, true, true, false, true],
    [false, true, false, true, true, true],
    [true, false, true, true, false, true, true, true],
    [true, true, false, true, false, true, true, true],
    [true, true, true, false, true, true, true, false, true],
    [true, false, true, true, false, true, true, false, true],
    [false],
    [false, true, false, true, false, true, true, true],
    [true, true, true, false, true, false, true, true, false, true],
    [false, true, true, true, false, true, true, true],
    [true, false, true, false, true, true, false, true]]

theorem hexWords_length : hexWords.length = 77 := rfl

theorem hexWords_ok : (hexadList.zip hexWords).all
    (fun p => decide (hexad0.map (wordPerm p.2).toEmbedding = p.1)) = true := by
  decide +kernel

theorem exists_smul_hexad0 {B : Finset (Fin 22)} (hB : B ∈ hexadList) :
    ∃ g : M22, g • hexad0 = B := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
  have hi' : i < (hexadList.zip hexWords).length := by
    rw [List.length_zip, hexWords_length, hexadList_checks'.1]
    rw [hexadList_checks'.1] at hi
    omega
  have h := List.all_eq_true.1 hexWords_ok _ (List.getElem_mem hi')
  rw [List.getElem_zip, decide_eq_true_eq] at h
  refine ⟨⟨wordPerm hexWords[i], wordPerm_mem _⟩, ?_⟩
  rw [Subgroup.smul_def, smul_finset_eq_map]
  exact h

theorem smul_mem_hexads_of_gen' {σ : Perm (Fin 22)} (hσ : σ = m22gA ∨ σ = m22gB)
    {B : Finset (Fin 22)} (hB : B ∈ hexads) : σ • B ∈ hexads := by
  have h5 := List.all_eq_true.1 hexadList_checks'.2.2.2.2 B (mem_hexads.1 hB)
  rw [Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at h5
  have hm : mask (σ • B) ∈ hexadMasks := by
    rw [smul_finset_eq_map]
    rcases hσ with rfl | rfl
    · exact h5.1
    · exact h5.2
  obtain ⟨C, hC, e⟩ := List.mem_map.1 hm
  rw [← mask_injective e]
  exact mem_hexads.2 hC

theorem smul_mem_hexads' (g : M22) {B : Finset (Fin 22)} (hB : B ∈ hexads) : g • B ∈ hexads := by
  have hgen : ∀ σ : Perm (Fin 22), (σ = m22gA ∨ σ = m22gB) → σ • hexads = hexads := by
    intro σ hσ
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro C hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.1 hC
      exact smul_mem_hexads_of_gen' hσ hB
    · rw [Finset.card_smul_finset]
  have hle : M22 ≤ stabilizer (Perm (Fin 22)) hexads := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro σ hσ
    exact hgen σ hσ
  have hg : (g : Perm (Fin 22)) • hexads = hexads := hle g.2
  rw [← hg, Subgroup.smul_def]
  exact Finset.smul_mem_smul_finset hB

theorem orbit_hexad0' : orbit M22 hexad0 = (hexads : Set (Finset (Fin 22))) := by
  ext B
  constructor
  · rintro ⟨g, rfl⟩
    exact smul_mem_hexads' g (mem_hexads.2 hexadList_checks'.2.2.1)
  · intro hB
    exact mem_orbit_iff.2 (exists_smul_hexad0 (mem_hexads.1 hB))

theorem m22Count_hexad0 :
    m22Count (fun g => ∀ x ∈ hexad0, g x ∈ hexad0) = 5760 := by
  have h : Nat.card (orbit M22 hexad0) * Nat.card (stabilizer M22 hexad0) = 443520 :=
    card_orbit_mul_card_stabilizer hexad0
  have hc : hexads.card = 77 := by
    rw [hexads, List.toFinset_card_of_nodup hexadList_checks'.2.1, hexadList_checks'.1]
  rw [orbit_hexad0', Nat.card_coe_set_eq, Set.ncard_coe_finset, hc] at h
  have hs : Nat.card (stabilizer M22 hexad0) = 5760 := by omega
  rw [← card_m22_subtype, ← hs]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_finset_iff.symm)

end CertificateChecks.KernelLC

end
