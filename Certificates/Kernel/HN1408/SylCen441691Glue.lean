module

public import Certificates.Kernel.HN1408.SylSGlue
public import Certificates.Kernel.HN1408.SylCen441691
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.EnumBaseSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylSG

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.BaseMask CFSG.KS.BaseEq
  CFSG.KS.RecGroup CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem syGen_spec {j : ℕ} (hj : j < 5) : syGen j < 2048 ∧ SylS.T (syGen j) = SylS.G j := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 syCen_hd j hj
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

namespace RecS

variable {x : ℕ → Equiv.Perm (Fin 1408)} (R : RecS x)
include R

theorem x_syGen {j : ℕ} (hj : j < 5) : x (syGen j) = elemW (sWords.getD j []) := by
  obtain ⟨hlt, he⟩ := syGen_spec hj
  have hr := R.rep _ hlt
  rw [he] at hr
  exact perm_eq_of_rep hr (gen_rep j hj).2

theorem syCenPt_iff {i : ℕ} (hi : i < 2048) :
    syCenPt 5 i = true ↔ ∀ j < 5, x i * elemW (sWords.getD j []) =
      elemW (sWords.getD j []) * x i := by
  unfold syCenPt
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h j hj
    have h' := h (4 - j) (by omega)
    have e : Nat.sub 5 (Nat.succ (4 - j)) = j := by
      change 5 - (4 - j + 1) = j
      omega
    rw [e] at h'
    rw [← R.x_syGen hj]
    exact R.comm_of_key hi (syGen_spec hj).1 h'
  · intro h j hj
    have hj' : Nat.sub 5 (Nat.succ j) < 5 := by
      change 5 - (j + 1) < 5
      omega
    refine R.key_of_comm hi (syGen_spec hj').1 ?_
    rw [R.x_syGen hj']
    exact h _ hj'

end RecS

theorem card_filter_range (n : ℕ) (f : ℕ → Bool) :
    ((Finset.range n).filter fun i => f i = true).card = (List.range n).countP f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append]
    by_cases hf : f n = true
    · rw [if_pos hf, Finset.card_insert_of_notMem (fun h => by simp at h), ih]
      simp [hf]
    · rw [if_neg hf, ih]
      simp [Bool.eq_false_iff.2 hf]

theorem card_subgroup_eq_ncard {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card H = (H : Set G).ncard :=
  Nat.card_coe_set_eq _

theorem card_center_S : Nat.card ↥(wordSubgroup sWords ⊓
    centralizer (wordSubgroup sWords : Set (Equiv.Perm (Fin 1408)))) = 4 := by
  classical
  obtain ⟨x, R⟩ := exists_recS
  have hset : ((wordSubgroup sWords ⊓
      centralizer (wordSubgroup sWords : Set (Equiv.Perm (Fin 1408))) : Subgroup _) :
        Set (Equiv.Perm (Fin 1408))) =
      (((Finset.range 2048).filter fun i => syCenPt 5 i = true).image x : Set _) := by
    ext g
    simp only [SetLike.mem_coe, mem_inf, Finset.coe_image, Finset.coe_filter, Finset.mem_range,
      Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hg, hgc⟩
      obtain ⟨i, hi, rfl⟩ := (R.mem _).1 hg
      refine ⟨i, ⟨hi, (R.syCenPt_iff hi).2 fun j hj => ?_⟩, rfl⟩
      have hw : sWords.getD j [] ∈ sWords := by
        rw [List.getD_eq_getElem _ _ (by rw [sWords_length]; exact hj)]
        exact List.getElem_mem _
      exact (mem_centralizer_iff.mp hgc _ (elemW_mem_wordSubgroup hw)).symm
    · rintro ⟨i, ⟨hi, hc⟩, rfl⟩
      refine ⟨R.mem_S hi, ?_⟩
      unfold wordSubgroup
      rw [centralizer_closure, mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      have hj' : j < 5 := by rwa [sWords_length] at hj
      have e := (R.syCenPt_iff hi).1 hc j hj'
      rw [List.getD_eq_getElem _ _ hj] at e
      exact e.symm
  rw [card_subgroup_eq_ncard, hset, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (fun a ha b hb e => R.inj a
      (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1) b
      (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1) e),
    card_filter_range, ← CFSG.KS.EnumBase.cntN_eq]
  exact Nat.eq_of_beq_eq_true syCen_cnt

theorem card_wordSubgroup_S : Nat.card ↥(wordSubgroup sWords) = 2 ^ 11 := by
  obtain ⟨x, R⟩ := exists_recS
  rw [card_of_mem_iff R.mem R.inj]
  norm_num

end CFSG.KD.HN1408.SylSG

end
