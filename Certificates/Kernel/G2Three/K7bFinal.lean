module

public import Certificates.Data.G23K7b
public import Certificates.Kernel.G2Three.K7bChecks
public import Certificates.Kernel.G2Three.Final
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.RankThree.PartTwo.Census.Carrier.G2Three Certificates.G2ThreeMax
  CFSG.CGT.PushingUpLit.CGT6.EmbModule

theorem bangA (a : Array ℕ) (n : ℕ) : a[n]! = a.getD n 0 := by
  rw [Array.getD_eq_getD_getElem?, getElem!_def]
  cases a[n]? <;> rfl

theorem bang_eq (a : Array ℕ) (n : ℕ) : a[n]! = a.toList.getD n 0 := by
  rw [bangA, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem mmul_toList (a b : Array ℕ) : (mmul a b).toList = mul14 a.toList b.toList := by
  unfold mmul mul14
  rw [Array.toList_ofFn, Array.toArray_toList, Array.toArray_toList]
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_map, List.length_range]
  · intro t h1 h2
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    unfold dot
    rw [list_sum_range]
    refine congrArg (· % 3) (Finset.sum_congr rfl fun l _ => ?_)
    unfold ent
    rw [bangA, bangA]

theorem idArr_toList : idArr.toList = one14 := by
  unfold idArr one14
  rw [Array.toList_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_map, List.length_range]
  · intro t h1 h2
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]

theorem canon_mmul (a b : Array ℕ) : canon14 (mmul a b).toList = true := by
  rw [mmul_toList]
  exact canon14_mul14 _ _

theorem pk_mmul {a b : Array ℕ} (ha : canon14 a.toList = true) (hb : canon14 b.toList = true) :
    pk (mmul a b).toList = MUL (pk a.toList) (pk b.toList) := by
  rw [mmul_toList]
  exact (mulE consts_ok ⟨ha, rfl⟩ ⟨hb, rfl⟩).2

theorem canon_idArr : canon14 idArr.toList = true := by
  rw [idArr_toList]
  exact canon14_one14

theorem pk_idArr : pk idArr.toList = ONE := by
  rw [idArr_toList]
  exact bone

theorem gen_at {k : ℕ}
    (h : (canon14 (genArr k).toList && Nat.beq (pk (genArr k).toList) (K7G k)) = true) (hk : k < 8) : canon14 (genArr k).toList = true ∧ pk (genArr k).toList = k7bGen K7G k := by
  rw [Bool.and_eq_true] at h
  have hb : Nat.blt k 8 = true := Nat.blt_eq.mpr hk
  unfold k7bGen
  rw [hb, cond_true]
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem gen_ok : ∀ k, canon14 (genArr k).toList = true ∧ pk (genArr k).toList = k7bGen K7G k
  | 0 => gen_at (by quickRfl) (by decide)
  | 1 => gen_at (by quickRfl) (by decide)
  | 2 => gen_at (by quickRfl) (by decide)
  | 3 => gen_at (by quickRfl) (by decide)
  | 4 => gen_at (by quickRfl) (by decide)
  | 5 => gen_at (by quickRfl) (by decide)
  | 6 => gen_at (by quickRfl) (by decide)
  | 7 => gen_at (by quickRfl) (by decide)
  | k + 8 => by
    have e : genArr (k + 8) = idArr := rfl
    have hb : Nat.blt (k + 8) 8 = false :=
      Bool.eq_false_iff.mpr fun h => absurd (Nat.blt_eq.mp h) (by omega)
    unfold k7bGen
    rw [e, hb, cond_false]
    exact ⟨canon_idArr, pk_idArr⟩

theorem canon_gen (k : ℕ) : canon14 (genArr k).toList = true := (gen_ok k).1

theorem pk_gen (k : ℕ) : pk (genArr k).toList = k7bGen K7G k := (gen_ok k).2

theorem word_ok (w : List ℕ) :
    canon14 (wordArr w).toList = true ∧ pk (wordArr w).toList = k7bWord K7G w := by
  induction w with
  | nil => exact ⟨canon_idArr, pk_idArr⟩
  | cons k w ih =>
    have e : wordArr (k :: w) = mmul (genArr k) (wordArr w) := by
      simp only [wordArr, List.foldr_cons]
    rw [e]
    refine ⟨canon_mmul _ _, ?_⟩
    rw [pk_mmul (canon_gen k) ih.1, pk_gen k, ih.2]
    simp only [k7bWord, List.foldr_cons]

theorem canon_word (w : List ℕ) : canon14 (wordArr w).toList = true := (word_ok w).1

theorem pk_word (w : List ℕ) : pk (wordArr w).toList = k7bWord K7G w := (word_ok w).2

theorem hg_ok (i : ℕ) :
    canon14 (kHgArr i).toList = true ∧ pk (kHgArr i).toList = k7bHg K7G i := by
  unfold kHgArr k7bHg
  split
  · exact word_ok _
  · unfold kCArr
    refine ⟨canon_mmul _ _, ?_⟩
    rw [pk_mmul (canon_word _) (canon_mmul _ _), pk_mmul (canon_word _) (canon_word _), pk_word,
      pk_word, pk_word]

theorem slp_ok (l : List ℕ) :
    canon14 (kSlpArr l).toList = true ∧ pk (kSlpArr l).toList = k7bSlpK K7G l := by
  induction l with
  | nil => exact ⟨canon_idArr, pk_idArr⟩
  | cons i l ih =>
    have e : kSlpArr (i :: l) = mmul (kHgArr i) (kSlpArr l) := by
      simp only [kSlpArr, List.foldr_cons]
    rw [e]
    refine ⟨canon_mmul _ _, ?_⟩
    rw [pk_mmul (hg_ok i).1 ih.1, (hg_ok i).2, ih.2]
    simp only [k7bSlpK, List.foldr_cons]

theorem canon_slp (l : List ℕ) : canon14 (kSlpArr l).toList = true := (slp_ok l).1

theorem pk_slp (l : List ℕ) : pk (kSlpArr l).toList = k7bSlpK K7G l := (slp_ok l).2

theorem beqA {a b : Array ℕ} (ha : canon14 a.toList = true) (hb : canon14 b.toList = true) :
    (a == b) = Nat.beq (pk a.toList) (pk b.toList) := by
  rw [← beq_pk ha hb]
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, fun h => Array.toList_inj.1 h⟩

theorem nz_eq {a : Array ℕ} (ha : canon14 a.toList = true) {p : ℕ} (hp : p < 196) :
    nzFlat a p = nzK (pk a.toList) p := by
  have hl := (canon14_iff.1 ha).1
  unfold nzFlat nzK
  rw [bang_eq, testBit_pk_lo hl hp, testBit_pk_hi hl hp]
  have h3 := getD_lt3 ha p
  generalize a.toList.getD p 0 = x at h3 ⊢
  interval_cases x <;> rfl

theorem k7bCheck_eq : k7bCheck = k7bK K7G := by
  simp only [k7bCheck, k7bK, kE8Arr, List.any_cons, List.any_nil,
    Bool.or_false, beqA, nz_eq, canon_mmul, canon_word, canon_slp, canon_gen, canon_idArr,
    pk_mmul, pk_word, pk_slp, pk_gen, pk_idArr, (by decide : 2 < 196), (by decide : 4 < 196),
    (by decide : 8 < 196), (by decide : 12 < 196)]

theorem k7bCheck_ok : k7bCheck = true := k7bCheck_eq.trans k7b271038_ok

end CFSG.KD.G2Three

end
