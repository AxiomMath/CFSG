module

public import Certificates.Kernel.UnitarySix.Sec3.G3600
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6
open CFSG.Monster.B.Co2 (allLt_iff)

theorem chS_k' : chS.ok = true ∧ chS.order = 32768 :=
  ⟨chS_K.facts'.1, chS_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chX1_k' : chX1.ok = true ∧ chX1.order = 4 :=
  ⟨chX1_K.facts'.1, chX1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chX2_k' : chX2.ok = true ∧ chX2.order = 4 :=
  ⟨chX2_K.facts'.1, chX2_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chX3_k' : chX3.ok = true ∧ chX3.order = 2 :=
  ⟨chX3_K.facts'.1, chX3_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chK1_k' : chK1.ok = true ∧ chK1.order = 25920 :=
  ⟨chK1_K.facts'.1, chK1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chK2_k' : chK2.ok = true ∧ chK2.order = 20160 :=
  ⟨chK2_K.facts'.1, chK2_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA1_k' : chA1.ok = true ∧ chA1.order = 512 :=
  ⟨chA1_K.facts'.1, chA1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA2_k' : chA2.ok = true ∧ chA2.order = 512 :=
  ⟨chA2_K.facts'.1, chA2_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chK1A1_k' : chK1A1.ok = true ∧ chK1A1.order = 13271040 :=
  ⟨chK1A1_K.facts'.1, chK1A1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chK2A2_k' : chK2A2.ok = true ∧ chK2A2.order = 10321920 :=
  ⟨chK2A2_K.facts'.1, chK2A2_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chL_k' : chL.ok = true ∧ chL.order = 9196830720 :=
  ⟨chL_K.facts'.1, chL_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chB12_k' : chB12.ok = true ∧ chB12.order = 60 :=
  ⟨chB12_K.facts'.1, chB12_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chB23_k' : chB23.ok = true ∧ chB23.order = 60 :=
  ⟨chB23_K.facts'.1, chB23_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chSJ_k' : chSJ.ok = true ∧ chSJ.order = 98304 :=
  ⟨chSJ_K.facts'.1, chSJ_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chT1_k' : chT1.ok = true ∧ chT1.order = 64 :=
  ⟨chT1_K.facts'.1, chT1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chT2_k' : chT2.ok = true ∧ chT2.order = 64 :=
  ⟨chT2_K.facts'.1, chT2_K.facts'.2.1.trans (by decide +kernel)⟩

section

variable {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
include hX

theorem sInt2_of' : (siftA 693 lvS chS.B 0 (conjA 693 au₂ (unpack 693 10 X)) ==
    siftA 693 lvT2 chT2.B 0 (unpack 693 10 X)) = sIntK2 (wK wu₂) (wKI wu₂) X := by
  have h2 := perm_words wu₂ (by simp)
  unfold sIntK2 au₂ lvS lvT2
  rw [wconj hX (w := wu₂) (by decide) h2, chS_K.sift' (conj_canon hX h2), chT2_K.sift' hX]
  rfl

theorem sInt1_of' : ((siftA 693 lvS chS.B 0 (conjA 693 au₁ (unpack 693 10 X)) ==
    siftA 693 lvT1 chT1.B 0 (unpack 693 10 X)) && (eqA 693 (unpack 693 10 X) (idA 693) ||
      !(siftA 693 lvS chS.B 0 (conjA 693 aw₀ (unpack 693 10 X))))) =
    sIntK1 (wK wu₁) (wKI wu₁) (wK ww₀) (wKI ww₀) X := by
  have h1 := perm_words wu₁ (by simp)
  have h0 := perm_words ww₀ (by simp)
  unfold sIntK1 au₁ aw₀ lvS lvT1
  rw [wconj hX (w := wu₁) (by decide) h1, wconj hX (w := ww₀) (by decide) h0,
    chS_K.sift' (conj_canon hX h1), chS_K.sift' (conj_canon hX h0), chT1_K.sift' hX, eq_id hX]
  rfl

theorem t2Int_of' : t2IntAt (unpack 693 10 X) =
    t2IntK (wK wab) (wKI wab) (wK wba) (wKI wba) (wK waba) (wKI waba) X := by
  have h1 := perm_words wab (by simp)
  have h2 := perm_words wba (by simp)
  have h3 := perm_words waba (by simp)
  unfold t2IntAt t2IntK aab aba aaba lvT2 lvX1 lvX2
  rw [wconj hX (w := wab) (by decide) h1, wconj hX (w := wba) (by decide) h2,
    wconj hX (w := waba) (by decide) h3, chT2_K.sift' (conj_canon hX h1),
    chT2_K.sift' (conj_canon hX h2), chT2_K.sift' (conj_canon hX h3), chX1_K.sift' hX,
    chX2_K.sift' hX, eq_id hX]
  rfl

theorem t1Int_of' : t1IntAt (unpack 693 10 X) = t1IntK (wK wbcb) (wKI wbcb) X := by
  have h1 := perm_words wbcb (by simp)
  unfold t1IntAt t1IntK abcb lvT1 lvX3
  rw [wconj hX (w := wbcb) (by decide) h1, chT1_K.sift' (conj_canon hX h1), chX3_K.sift' hX]
  rfl

theorem ka1_of' : ka1At (unpack 693 10 X) = ka1K X := by
  unfold ka1At ka1K lvK1
  rw [chK1_K.sift' hX, eq_id hX, unpack_get (by norm_num)]
  rfl

theorem ka2_of' : ka2At (unpack 693 10 X) = ka2K (wK wu₂) (wKI wu₂) X := by
  have h1 := perm_words wu₂ (by simp)
  unfold ka2At ka2K au₂ lvK2 lvK2A2
  rw [wconj hX (w := wu₂) (by decide) h1, chK2A2_K.sift' (conj_canon hX h1), chK2_K.sift' hX,
    eq_id hX]
  rfl

end

theorem normK_of' {X : ℕ} (h : normK X = true) :
    (!(chS.O.all fun s => siftA 693 lvS chS.B 0 (conjA 693 (unpack 693 10 X) s)) ||
      siftA 693 lvSJ chSJ.B 0 (unpack 693 10 X)) = true := by
  unfold normK at h
  rw [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨hp, h⟩ := h
  have hX := PermK.canon hp
  unfold lvS lvSJ
  rw [chS_K.O_all, chSJ_K.sift' hX]
  have e : ∀ j ∈ List.range 5, siftA 693 chS.levels chS.B 0
      (conjA 693 (unpack 693 10 X) (unpack 693 10 (CS.S j))) =
      sfS (pcomp 693 10 (mask 10) X
        (pcomp 693 10 (mask 10) (CS.S j) (pinvS 693 10 (mask 10) X))) := by
    intro j hj
    have hj' := chS_P j (List.mem_range.1 hj)
    rw [conj_unpack hp (PermK.canon hj'),
      chS_K.sift' (canon_comp hX (canon_comp (PermK.canon hj') (PermK.canon_inv hp)))]
    rfl
  have hl : chS.gens.length = 5 := rfl
  have e2 : ((List.range 5).all fun j => siftA 693 chS.levels chS.B 0
      (conjA 693 (unpack 693 10 X) (unpack 693 10 (CS.S j)))) = (List.range 5).all fun j =>
      sfS (pcomp 693 10 (mask 10) X
        (pcomp 693 10 (mask 10) (CS.S j) (pinvS 693 10 (mask 10) X))) :=
    Bool.eq_iff_iff.2 (by
      simp only [List.all_eq_true]
      exact forall₂_congr fun j hj => by rw [e j hj])
  rw [hl, e2]
  exact h

section

variable {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
include hL

theorem sInt_L' (h : sIntL (wK wu₂) (wKI wu₂) (wK wu₁) (wKI wu₁) (wK ww₀) (wKI ww₀) L = true) :
    sIntAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = true := by
  have hX := prodL_canon hL
  unfold sIntL at h
  rw [strictB_eq, strictB_eq] at h
  unfold sIntAt
  rw [prodL_get hL (by norm_num : 381 < 693), prodL_get hL (by norm_num : 1 < 693), sInt2_of' hX,
    sInt1_of' hX]
  exact h

theorem norm_L' (h : normL L = true) :
    normAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = true := by
  have hX := prodL_canon hL
  unfold normL at h
  unfold normAt
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have h' : ((List.range 6).all fun j => pg 10 (mask 10) sec3LabT1
        (ptL 10 (mask 10) L (pg 10 (mask 10) (CT1.S j) 9)) == pg 10 (mask 10) sec3LabT1
        (ptL 10 (mask 10) L 9)) = false := by simpa using h
    have hl : chT1.gens.length = 6 := rfl
    have e : ∀ j ∈ List.range 6, (labT1[(unpack 693 10 (prodL 693 10 (mask 10) L))[
        (unpack 693 10 (CT1.S j))[9]!]!]! ==
        labT1[(unpack 693 10 (prodL 693 10 (mask 10) L))[9]!]!) =
        (pg 10 (mask 10) sec3LabT1 (ptL 10 (mask 10) L (pg 10 (mask 10) (CT1.S j) 9)) ==
          pg 10 (mask 10) sec3LabT1 (ptL 10 (mask 10) L 9)) := by
      intro j hj
      have hj' := PermK.canon (chT1_P j (List.mem_range.1 hj))
      have h9 : pg 10 (mask 10) (CT1.S j) 9 < 693 := canon_lt hj' (by norm_num)
      have b1 : ptL 10 (mask 10) L (pg 10 (mask 10) (CT1.S j) 9) < 693 := by
        rw [← prodL_get hL h9, unpack_get h9]
        exact canon_lt hX h9
      have b2 : ptL 10 (mask 10) L 9 < 693 := by
        rw [← prodL_get hL (by norm_num), unpack_get (by norm_num)]
        exact canon_lt hX (by norm_num)
      rw [unpack_get (by norm_num : 9 < 693), prodL_get hL h9, prodL_get hL (by norm_num),
        labT1_eq _ b1, labT1_eq _ b2]
    have e2 : ((List.range 6).all fun j => labT1[(unpack 693 10 (prodL 693 10 (mask 10) L))[
        (unpack 693 10 (CT1.S j))[9]!]!]! ==
        labT1[(unpack 693 10 (prodL 693 10 (mask 10) L))[9]!]!) = (List.range 6).all fun j =>
        pg 10 (mask 10) sec3LabT1 (ptL 10 (mask 10) L (pg 10 (mask 10) (CT1.S j) 9)) ==
          pg 10 (mask 10) sec3LabT1 (ptL 10 (mask 10) L 9) :=
      Bool.eq_iff_iff.2 (by
        simp only [List.all_eq_true]
        exact forall₂_congr fun j hj => by rw [e j hj])
    have hA : (chT1.O.all fun s => labT1[(unpack 693 10 (prodL 693 10 (mask 10) L))[s[9]!]!]! ==
        labT1[(unpack 693 10 (prodL 693 10 (mask 10) L))[9]!]!) = false := by
      rw [chT1_K.O_all, hl, e2]
      exact h'
    rw [hA]
    rfl
  · rw [Bool.or_assoc, normK_of' h, Bool.or_true]

end

theorem uNorm_k' : uNormCheck = true := by
  have hk := kU
  rw [Bool.and_eq_true] at hk
  unfold uNormCheck lvK1 lvK2
  rw [chK1_K.O_all, chK2_K.O_all, Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun j hj => ?_⟩
  · have hj' := chK1_P j (List.mem_range.1 hj)
    have hp := perm_words wu₁ (by simp)
    rw [au₁, wconj (PermK.canon hj') (w := wu₁) (by decide) hp,
      chK1_K.sift' (conj_canon (PermK.canon hj') hp)]
    exact List.all_eq_true.1 hk.1 j hj
  · have hj' := chK2_P j (List.mem_range.1 hj)
    have hp := perm_words wu₂ (by simp)
    rw [au₂, wconj (PermK.canon hj') (w := wu₂) (by decide) hp,
      chK2_K.sift' (conj_canon (PermK.canon hj') hp)]
    exact List.all_eq_true.1 hk.2 j hj

theorem kNorm_k' : kNormCheck = true := by
  have hk := kKN
  rw [Bool.and_eq_true] at hk
  unfold kNormCheck lvA1 lvA2
  rw [chK1_K.O_all, chK2_K.O_all, Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun j hj => ?_⟩
  · rw [chA1_K.O_all]
    refine List.all_eq_true.2 fun i hi => ?_
    have hj' := chK1_P j (List.mem_range.1 hj)
    have hi' := PermK.canon (chA1_P i (List.mem_range.1 hi))
    rw [conj_unpack hj' hi', chA1_K.sift' (conj_canon hi' hj')]
    exact List.all_eq_true.1 (List.all_eq_true.1 hk.1 j hj) i hi
  · rw [chA2_K.O_all]
    refine List.all_eq_true.2 fun i hi => ?_
    have hj' := chK2_P j (List.mem_range.1 hj)
    have hi' := PermK.canon (chA2_P i (List.mem_range.1 hi))
    rw [conj_unpack hj' hi', chA2_K.sift' (conj_canon hi' hj')]
    exact List.all_eq_true.1 (List.all_eq_true.1 hk.2 j hj) i hi

theorem sNorm_k' : sNormCheck = true := by
  have hk := kSN
  rw [Bool.and_eq_true] at hk
  unfold sNormCheck lvS
  rw [chS_K.O_all, Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun k hk' => ?_⟩
  · have hj' := chS_P j (List.mem_range.1 hj)
    have hp := perm_words wj₀ (by simp)
    rw [aj₀, wconj (PermK.canon hj') (w := wj₀) (by decide) hp,
      chS_K.sift' (conj_canon (PermK.canon hj') hp)]
    exact List.all_eq_true.1 hk.1 j hj
  · have h15 := List.mem_range.1 hk'
    rw [hG k (by omega), chS_K.sift' (hc k (by omega))]
    exact List.all_eq_true.1 hk.2 k hk'

theorem t1K1_k' : t1K1Check = true := by
  unfold t1K1Check lvK1
  rw [chT1_K.O_all]
  refine List.all_eq_true.2 fun j hj => ?_
  rw [chK1_K.sift' (PermK.canon (chT1_P j (List.mem_range.1 hj)))]
  exact List.all_eq_true.1 kT1K1 j hj

end CertificateChecks.KernelU6.Sec3
