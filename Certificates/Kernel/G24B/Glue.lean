module

public import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound
public import Certificates.Kernel.Misc.G24Facts
import CFSG.Quasithin.Background.TwoM22TwoModelOfGens
public import CFSG.Certificates.Kernel.Misc.G24P0Sound
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts
public import Certificates.Kernel.G24B.Recs

public section

noncomputable section

namespace CFSG.KD.G24B

open CFSG.Fischer CFSG.Quasithin.F112R.St84.G24M CFSG.KC.Misc.Spec CFSG.KC.F2BfsRec
open CFSG.LieType.Multipliers.G24 (toMat_ofMat)


@[expose] def psi : Y →* Matrix (Fin 28) (Fin 28) (ZMod 2) where
  toFun y := blowMat (toGL y : Matrix (Fin 14) (Fin 14) F4)
  map_one' := by rw [map_one, Units.val_one, blowMat_one]
  map_mul' x y := by rw [map_mul, Units.val_mul, blowMat_mul]

theorem psi_apply (y : Y) : psi y = blowMat (toGL y : Matrix (Fin 14) (Fin 14) F4) := rfl

theorem psi_injective (hC : ChevFacts) : Function.Injective (psi : Y →* _) :=
  fun x y h => hC.toGL_injective (Units.ext (blowMat_injective h))

theorem lettersOf_eq (w : List (Fin 6 × Bool)) : lettersOf w = encG w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    change (2 * i.val + Bool.rec 0 1 b) :: lettersOf w = encL (i, b) :: encG w
    rw [ih]
    cases b <;> rfl

theorem psi_agY (hC : ChevFacts) (w : List (Fin 6 × Bool)) : psi (agY w) = pkMat 28 (blowW w) := by
  have e0 : CFSG.KC.Misc.G24.wordArrOf
      (CFSG.KC.Misc.G24.genArrsOf CFSG.LieType.Multipliers.G24.genRows) w =
      CFSG.LieType.Multipliers.G24.wordArr w := by
    simp only [CFSG.KC.Misc.G24.wordArrOf, CFSG.KC.Misc.G24.genArrsOf,
      CFSG.LieType.Multipliers.G24.wordArr, CFSG.LieType.Multipliers.G24.genArr,
      CFSG.LieType.Multipliers.G24.genArrs]
  rw [psi_apply, hC.toGL_agY, blowW, lettersOf_eq,
    CFSG.KC.Misc.G24.g24F4_word CFSG.KD.Misc.G24.k44 w, CFSG.KC.Misc.G24.g24Mat,
    ← CFSG.KD.Misc.G24.bG, e0]

theorem pk_eq (X : ℕ) : CFSG.KC.WordPts.matOfF 28 X = pkMat 28 X := matOfF_eq_pkMat 28 X

structure RecOK {ng : ℕ} (S : Fin ng → Y) (lb : ℕ) (CF G : ℕ → ℕ) (N : ℕ) : Prop where
  hS : ∀ j : Fin ng, psi (S j) = pkMat 28 (G j)
  hN : 0 < N
  hNw : N < 2 ^ 12
  hh : headK 28 12 lb ng CF = true
  h : ∀ k < N, recK2 28 12 lb ng CF G N k = true

variable {ng lb N : ℕ} {S : Fin ng → Y} {CF G : ℕ → ℕ}

def genIn (S : Fin ng → Y) (j : Fin ng) : ↥(Subgroup.closure (Set.range S)) :=
  ⟨S j, Subgroup.subset_closure ⟨j, rfl⟩⟩

theorem closure_genIn_top (S : Fin ng → Y) :
    Subgroup.closure {x | (∃ j, genIn S j = x) ∨ (psi.comp (Subgroup.closure (Set.range S)).subtype) x = 1} = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← CFSG.GroupTheory.closure_range_subtype_eq_top S]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨j, rfl⟩
  exact Or.inl ⟨j, rfl⟩

theorem card_of_recOK (hC : ChevFacts) (hR : RecOK S lb CF G N) :
    Nat.card (Subgroup.closure (Set.range S)) = N := by
  have hc := card_range_of_recK2 (psi.comp (Subgroup.closure (Set.range S)).subtype) (genIn S)
    (fun j => by rw [pk_eq]; exact hR.hS j) (closure_genIn_top S) hR.hN hR.hNw hR.hh hR.h
  rw [← hc, Nat.card_range_of_injective]
  exact (psi_injective hC).comp Subtype.val_injective

theorem exists_entry_of_recOK (hR : RecOK S lb CF G N) {y : Y}
    (hy : y ∈ Subgroup.closure (Set.range S)) :
    ∃ t < N, psi y = pkMat 28 (elemAt 28 12 lb ng CF t) := by
  obtain ⟨t, ht, he⟩ := exists_entry_of_recK2 (psi.comp (Subgroup.closure (Set.range S)).subtype)
    (genIn S) (fun j => by rw [pk_eq]; exact hR.hS j) (closure_genIn_top S) hR.hN hR.hNw hR.hh
    hR.h ⟨y, hy⟩
  exact ⟨t, ht, by rw [← pk_eq]; exact he⟩

theorem exists_mem_of_recOK (hR : RecOK S lb CF G N) {t : ℕ} (ht : t < N) :
    ∃ y ∈ Subgroup.closure (Set.range S), psi y = pkMat 28 (elemAt 28 12 lb ng CF t) := by
  obtain ⟨⟨y, hy⟩, he⟩ := exists_of_entry_recK2 (psi.comp (Subgroup.closure (Set.range S)).subtype)
    (genIn S) (fun j => by rw [pk_eq]; exact hR.hS j) hR.hN hR.hNw hR.hh hR.h ht
  exact ⟨y, hy, by rw [← pk_eq]; exact he⟩

theorem eq_of_pk {X Z : ℕ} (hX : X < 2 ^ (28 * 28)) (hZ : Z < 2 ^ (28 * 28))
    (h : pkMat 28 X = pkMat 28 Z) : X = Z :=
  CFSG.KC.F2Mat.matOfF_inj hX hZ (by rw [pk_eq, pk_eq, h])

theorem not_mem_of_gap (hR : RecOK S lb CF G N) {p X : ℕ} {y : Y} (hX : X < 2 ^ (28 * 28))
    (hy : psi y = pkMat 28 X) (hg : gapK 28 12 lb ng CF N p X = true) :
    y ∉ Subgroup.closure (Set.range S) := by
  intro hm
  obtain ⟨t, ht, he⟩ := exists_entry_of_recOK hR hm
  exact ne_of_gapK hR.h hg t ht (eq_of_pk (CFSG.KC.F2Mat.elemAt_lt _ _ _ _ _ _) hX
    (he.symm.trans hy))

theorem mem_of_sorted (hC : ChevFacts) (hR : RecOK S lb CF G N) {s : ℕ} {y : Y} (hs : s < N)
    (hy : psi y = pkMat 28 (sortedAt 28 12 lb ng CF s)) :
    y ∈ Subgroup.closure (Set.range S) := by
  obtain ⟨t, ht, e⟩ := sortedAt_entry hR.h hs
  obtain ⟨z, hz, hze⟩ := exists_mem_of_recOK hR ht
  rw [psi_injective hC (hy.trans (e ▸ hze.symm))]
  exact hz

theorem exists_mem_of_sorted (hR : RecOK S lb CF G N) {s : ℕ} (hs : s < N) :
    ∃ y ∈ Subgroup.closure (Set.range S), psi y = pkMat 28 (sortedAt 28 12 lb ng CF s) := by
  obtain ⟨t, ht, e⟩ := sortedAt_entry hR.h hs
  rw [e]
  exact exists_mem_of_recOK hR ht

theorem mulF2_lt' (A B : ℕ) : CFSG.KC.Misc.G24.mulF2 28 A B < 2 ^ (28 * 28) := mulF2_lt 28 A B

set_option exponentiation.threshold 1000 in
theorem oneF2_lt : CFSG.KC.Misc.G24.oneF2 28 < 2 ^ (28 * 28) := by decide +kernel

theorem wordF4_lt (L u : List ℕ) : CFSG.KC.Misc.G24.wordF4 L u < 2 ^ (28 * 28) := by
  cases u with
  | nil => exact oneF2_lt
  | cons c u => exact mulF2_lt' _ _

theorem pk_one_iff {X : ℕ} (hX : X < 2 ^ (28 * 28)) :
    pkMat 28 X = 1 ↔ X = CFSG.KC.Misc.G24.oneF2 28 := by
  constructor
  · intro h
    exact eq_of_pk hX oneF2_lt (h.trans (pkMat_oneF2 28).symm)
  · rintro rfl
    exact pkMat_oneF2 28

end CFSG.KD.G24B
