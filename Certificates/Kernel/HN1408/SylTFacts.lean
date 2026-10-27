module

public import Certificates.Kernel.HN1408.SylTChk
public import Certificates.Kernel.HN1408.SylSGlue
public import Certificates.Kernel.HN1408.CzTScan
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylTF

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BaseMask
  CFSG.KS.RecGroup CFSG.KD.HN1408 CFSG.KD.HN1408.SylSG CFSG.KD.HN1408.SylT CFSG.KS.MulH
  CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def Swap (g : Equiv.Perm (Fin 1408)) : Prop := ∀ i : Fin 1408, (g i).val < 704 ↔ ¬ i.val < 704

theorem blk_or_swap_closure {s : Set (Equiv.Perm (Fin 1408))}
    (hs : ∀ g ∈ s, g ∈ blocks1408 ∨ Swap g) : ∀ g ∈ closure s, g ∈ blocks1408 ∨ Swap g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy => exact hs y hy
  | one => exact Or.inl (one_mem _)
  | mul y z _ _ hy hz =>
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact Or.inl (mul_mem hy hz)
    · right
      intro i
      rw [Equiv.Perm.mul_apply]
      exact (hy (z i)).trans (hz i)
    · right
      intro i
      rw [Equiv.Perm.mul_apply]
      exact (hy (z i)).trans (not_congr (hz i))
    · left
      intro i
      rw [Equiv.Perm.mul_apply, hy (z i), hz i, not_not]
  | inv y _ hy =>
    rcases hy with hy | hy
    · exact Or.inl (inv_mem hy)
    · right
      intro i
      have h := hy (y⁻¹ i)
      have e : y (y⁻¹ i) = i := by simp
      rw [e] at h
      tauto

theorem bIf_not_iff (u v : Bool) : bIf(u, v, bIf(v, false, true)) = true ↔ (u = true ↔ v = true) := by
  cases u <;> cases v <;> decide

theorem bIf_swap_iff (u v : Bool) : bIf(u, bIf(v, false, true), v) = true ↔
    (u = true ↔ ¬ v = true) := by
  cases u <;> cases v <;> decide

theorem blkGenK_spec {G : Nat} {g : Equiv.Perm (Fin 1408)}
    (hG : ∀ p (hp : p < 1408), pt G p = (g ⟨p, hp⟩).val) (h : blkGenK G = true) :
    g ∈ blocks1408 ∨ Swap g := by
  unfold blkGenK at h
  rw [Orb.bIf_eq] at h
  split_ifs at h with h1
  · left
    intro i
    have h2 := Orb.allN_iff.1 h1 i.val i.isLt
    rw [Orb.strictB_eq, bIf_not_iff, Nat.blt_eq, Nat.blt_eq, hG i.val i.isLt] at h2
    exact h2
  · right
    intro i
    have h2 := Orb.allN_iff.1 h i.val i.isLt
    rw [Orb.strictB_eq, bIf_swap_iff, Nat.blt_eq, Nat.blt_eq, hG i.val i.isLt] at h2
    exact h2

theorem pt_of_rep {X : Nat} {σ : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (h : Rep 1408 (tabT (unpack 1408 11 X)) σ) (p : Nat) (hp : p < 1408) :
    pt X p = (σ ⟨p, hp⟩).val := by
  unfold pt
  rw [pt_rep hX h hp, idx_of_lt σ hp, Equiv.Perm.smul_def]

theorem blk_or_swap : ∀ g ∈ wordSubgroup sWords, g ∈ blocks1408 ∨ Swap g := by
  refine blk_or_swap_closure ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have hj5 : j < 5 := by rw [← sWords_length]; exact hj
  obtain ⟨c, r⟩ := gen_rep j hj5
  rw [← List.getD_eq_getElem _ [] hj]
  exact blkGenK_spec (pt_of_rep c r) (Orb.allN_iff.1 genBlk_ok j hj5)

theorem mem_blocks_iff {g : Equiv.Perm (Fin 1408)} (hg : g ∈ wordSubgroup sWords) :
    g ∈ blocks1408 ↔ (g ⟨0, by norm_num⟩).val < 704 := by
  constructor
  · intro h
    exact (h ⟨0, by norm_num⟩).2 (by norm_num)
  · intro h0
    rcases blk_or_swap g hg with h | h
    · exact h
    · exact absurd ((h ⟨0, by norm_num⟩).1 h0) (by norm_num)

theorem foldr_count (q : ℕ → Bool) (l : List ℕ) :
    l.foldr (fun i s => if q i = true then Nat.succ s else s) 0 = l.countP q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.countP_cons]
    cases q a <;> simp

theorem cntN_eq (n : ℕ) (q : ℕ → Bool) : cntN n q = (List.range n).countP q := by
  unfold cntN
  rw [Orb.foldN_eq]
  simp only [Orb.nIf_eq]
  exact foldr_count q _

theorem ncard_count {G : Type*} {f : ℕ → G} {n : ℕ}
    (hinj : ∀ a < n, ∀ b < n, f a = f b → a = b) (P : G → Prop) (q : ℕ → Bool)
    (hq : ∀ i < n, q i = true ↔ P (f i)) :
    {g | (∃ i < n, f i = g) ∧ P g}.ncard = (List.range n).countP q := by
  classical
  have e : {g | (∃ i < n, f i = g) ∧ P g} = f '' (((List.range n).filter q).toFinset : Set ℕ) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset,
      List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hP⟩
      exact ⟨i, ⟨hi, (hq i hi).2 hP⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hqi⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (hq i hi).1 hqi⟩
  rw [e, Set.InjOn.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (List.nodup_range.filter _), ← List.countP_eq_length_filter]
  intro a ha b hb hab
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at ha hb
  exact hinj a ha.1 b hb.1 hab

theorem cent_rows : ∀ i < 2048, centRowK (r32 SylS.FM 2) (r32 SylS.FM 1) (r32 SylS.FM 3)
    (r32 TG 0) (r32 TG 1) (r32 TG 2) i = true := by
  have h := cent_ok
  unfold centK at h
  simp only [Orb.strictB_eq] at h
  exact Orb.allN_iff.1 h

end CFSG.KD.HN1408.SylTF

namespace CFSG.KD.HN1408.SylSG.RecS

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BaseMask
  CFSG.KS.RecGroup CFSG.KD.HN1408 CFSG.KD.HN1408.SylSG CFSG.KD.HN1408.SylT CFSG.KS.MulH
  CFSG.KC.BfsPin CFSG.KD.HN1408.SylTF
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

variable {x : ℕ → Equiv.Perm (Fin 1408)} (R : RecS x)
include R

theorem ent_word {s : ℕ} (hs : s < 2048) {w : List ℕ} (hw : lettersOK w = true)
    (h : SylS.T s = WK w) : x s = elemW w := by
  have r := R.rep s hs
  rw [h] at r
  exact perm_eq_of_rep r (rep_word hw).1

theorem ent_gen {j : ℕ} (hj : j < 5) : x (j + 1) = elemW (sWords.getD j []) := by
  have e : SylS.T (Nat.succ j) = SylS.G j :=
    Nat.eq_of_beq_eq_true (Orb.allN_iff.1 genIdx_ok j hj)
  have r := R.rep (j + 1) (by omega)
  rw [Nat.succ_eq_add_one] at e
  rw [e] at r
  exact perm_eq_of_rep r (gen_rep j hj).2

theorem ent_blocks {i : ℕ} (hi : i < 2048) : x i ∈ blocks1408 ↔ halfB i = true := by
  rw [mem_blocks_iff (R.mem_S hi), halfB, Nat.blt_eq, pt_of_rep (R.canon i hi) (R.rep i hi) 0
    (by norm_num)]

theorem fm_lt {e : ℕ} (he : e < 4) : r32 SylS.FM e < 2048 := by
  obtain ⟨-, -, -, hlt⟩ := R.member (by norm_num) R.member_V
  have h := hlt e (by norm_num; omega)
  rwa [Nat.zero_add] at h

theorem ent_a : x (r32 SylS.FM 1) = elemA := by
  have h := sylS_az
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact R.ent_word (R.fm_lt (by norm_num)) (by decide) (Nat.eq_of_beq_eq_true h.1)

theorem ent_z : x (r32 SylS.FM 2) = elemZ := by
  have h := sylS_az
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact R.ent_word (R.fm_lt (by norm_num)) (by decide) (Nat.eq_of_beq_eq_true h.2)

theorem ent_az : x (r32 SylS.FM 3) = elemA * elemZ := by
  have h := R.step R.member_V (e := 1) (j := 1) (by norm_num) (by norm_num)
  have e1 : (2 : ℕ) ^ 1 = 2 := rfl
  have e3 : (1 : ℕ) ^^^ 2 = 3 := by decide
  rw [e1] at h
  simp only [Nat.zero_add, e3] at h
  rw [← R.ent_a, ← R.ent_z, h]

theorem sylow_card : Nat.card ↥(wordSubgroup sWords) = 2 ^ 11 := by
  rw [card_of_mem_iff R.mem R.inj]
  norm_num

theorem a_mem : elemA ∈ wordSubgroup sWords := R.ent_a ▸ R.mem_S (R.fm_lt (by norm_num))

theorem z_mem : elemZ ∈ wordSubgroup sWords := R.ent_z ▸ R.mem_S (R.fm_lt (by norm_num))

theorem z_comm {g : Equiv.Perm (Fin 1408)} (hg : g ∈ wordSubgroup sWords) :
    elemZ * g = g * elemZ := by
  have hz : elemZ ∈ memG x SylS.FM 0 2 := by
    rw [← R.ent_z]
    exact subset_closure ⟨1, by norm_num, rfl⟩
  exact (R.V_cent hz hg).symm

theorem tgK_parts : (∀ l < 3, r32 TG l < 2048 ∧ SylS.T (r32 TG l) = WK (tGens.getD l []) ∧
    halfB (r32 TG l) = true) ∧ halfB (r32 SylS.FM 1) = true ∧ halfB (r32 SylS.FM 2) = true := by
  have h := tg_ok
  unfold tgK at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun l hl => ?_, h.2.1, h.2.2⟩
  have h1 := Orb.allN_iff.1 h.1 l hl
  rw [Orb.strictB_eq] at h1
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2.1, h1.2.2⟩

theorem tGens_letters {l : ℕ} (hl : l < 3) : lettersOK (tGens.getD l []) = true := by
  interval_cases l <;> decide

theorem ent_tg {l : ℕ} (hl : l < 3) : x (r32 TG l) = elemW (tGens.getD l []) :=
  R.ent_word (R.tgK_parts.1 l hl).1 (R.tGens_letters hl) (R.tgK_parts.1 l hl).2.1

theorem tg_T {l : ℕ} (hl : l < 3) : elemW (tGens.getD l []) ∈ wordSubgroup sWords ∧
    elemW (tGens.getD l []) ∈ blocks1408 := by
  rw [← R.ent_tg hl]
  exact ⟨R.mem_S (R.tgK_parts.1 l hl).1,
    (R.ent_blocks (R.tgK_parts.1 l hl).1).2 (R.tgK_parts.1 l hl).2.2⟩

theorem z_blocks : elemZ ∈ blocks1408 := by
  rw [← R.ent_z]
  exact (R.ent_blocks (R.fm_lt (by norm_num))).2 R.tgK_parts.2.2

theorem a_blocks : elemA ∈ blocks1408 := by
  rw [← R.ent_a]
  exact (R.ent_blocks (R.fm_lt (by norm_num))).2 R.tgK_parts.2.1

theorem centRow_spec {z a c t0 t1 t2 i : ℕ} (h : centRowK z a c t0 t1 t2 i = true)
    (hh : halfB i = true) (h0 : commKeyK 11 (mask 11) 2 0 SylS.T i t0 = true)
    (h1 : commKeyK 11 (mask 11) 2 0 SylS.T i t1 = true)
    (h2 : commKeyK 11 (mask 11) 2 0 SylS.T i t2 = true) : i = 0 ∨ i = a ∨ i = z ∨ i = c := by
  unfold centRowK at h
  rw [Orb.bIf_eq, if_pos hh, Orb.bAnd_eq, Bool.and_eq_true, Orb.bIf_eq] at h
  rw [if_pos (by rw [Orb.bAnd_eq, Orb.bAnd_eq, h0, h1, h2]; rfl)] at h
  have h3 := h.2
  simp only [Orb.bIf_eq] at h3
  by_cases e0 : Nat.beq i 0 = true
  · exact Or.inl (Nat.eq_of_beq_eq_true e0)
  rw [if_neg e0] at h3
  by_cases ea : Nat.beq i a = true
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true ea))
  rw [if_neg ea] at h3
  by_cases ez : Nat.beq i z = true
  · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true ez)))
  rw [if_neg ez] at h3
  exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h3)))

theorem centre_T {g : Equiv.Perm (Fin 1408)} (hg : g ∈ wordSubgroup sWords)
    (hE : g ∈ blocks1408)
    (hc : ∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 → g * y = y * g) :
    g = 1 ∨ g = elemA ∨ g = elemZ ∨ g = elemA * elemZ := by
  obtain ⟨i, hi, rfl⟩ := (R.mem g).1 hg
  have hk : ∀ l < 3, commKeyK 11 (mask 11) 2 0 SylS.T i (r32 TG l) = true := by
    intro l hl
    have hT := R.tg_T hl
    rw [← R.ent_tg hl] at hT
    exact R.key_of_comm hi (R.tgK_parts.1 l hl).1 (hc _ hT.1 hT.2)
  have hh : halfB i = true := (R.ent_blocks hi).1 hE
  rcases R.centRow_spec (cent_rows i hi) hh (hk 0 (by norm_num)) (hk 1 (by norm_num))
      (hk 2 (by norm_num)) with e | e | e | e
  · left
    rw [e, R.one]
  · right; left
    rw [e, R.ent_a]
  · right; right; left
    rw [e, R.ent_z]
  · right; right; right
    rw [e, R.ent_az]

theorem cent_T_le (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)} (hg : g ∈ P1408)
    (hc : ∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 → g * y = y * g) : g ∈ blocks1408 := by
  have hz : g * elemZ = elemZ * g := hc _ R.z_mem R.z_blocks
  have hx : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
    mem_inf.2 ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hz⟩
  have ht : ∀ w ∈ tGens, g * elemW w = elemW w * g := by
    intro w hw
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hw
    have hl3 : l < 3 := lt_of_lt_of_eq hl (by decide)
    rw [← List.getD_eq_getElem _ [] hl]
    exact hc _ (R.tg_T hl3).1 (R.tg_T hl3).2
  rcases CFSG.KD.HN1408.CzT.cent_tGens hP hx ht with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact R.a_blocks
  · exact R.z_blocks
  · exact mul_mem R.a_blocks R.z_blocks

end CFSG.KD.HN1408.SylSG.RecS

end
