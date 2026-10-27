module

public import Certificates.Kernel.HN1408.TableKGrp

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.BfsPin CFSG.KC.Blk CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HNRecog.HaradaModel

def SwH (g : Equiv.Perm (Fin 1408)) : Prop := ∀ i : Fin 1408, ((g i).val < 704 ↔ ¬ i.val < 704)

theorem pres_of {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (h : halvesK X = true) :
    g ∈ blocks1408 := by
  rintro ⟨i, hi⟩
  change (g ⟨i, hi⟩).val < 704 ↔ i < 704
  rw [← repC_pt hX hi]
  by_cases h704 : i < 704
  · have h' := allN_spec h i h704
    simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
    obtain ⟨h1, -⟩ := h'
    exact ⟨fun _ => h704, fun _ => h1⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = 704 + k := ⟨i - 704, by omega⟩
    have h' := allN_spec h k (by omega)
    simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
    obtain ⟨-, h2⟩ := h'
    constructor
    · intro h3
      omega
    · intro h3
      omega

theorem swap_of {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (h : swapsK X = true) :
    SwH g := by
  rintro ⟨i, hi⟩
  change (g ⟨i, hi⟩).val < 704 ↔ ¬ i < 704
  rw [← repC_pt hX hi]
  by_cases h704 : i < 704
  · have h' := allN_spec h i h704
    simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
    obtain ⟨h1, -⟩ := h'
    constructor
    · intro h3
      omega
    · intro h3
      exact absurd h704 h3
  · obtain ⟨k, rfl⟩ : ∃ k, i = 704 + k := ⟨i - 704, by omega⟩
    have h' := allN_spec h k (by omega)
    simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
    obtain ⟨-, h2⟩ := h'
    exact ⟨fun _ => h704, fun _ => h2⟩

theorem not_mem_of_swH {g : Equiv.Perm (Fin 1408)} (hg : SwH g) : g ∉ blocks1408 := by
  intro hb
  have h1 := hg ⟨0, by norm_num⟩
  have h2 : (g ⟨0, by norm_num⟩).val < 704 ↔ (0 : Nat) < 704 := hb ⟨0, by norm_num⟩
  have h3 : (0 : Nat) < 704 := by norm_num
  exact h1.1 (h2.2 h3) h3

theorem swH_mul_swH {g h : Equiv.Perm (Fin 1408)} (hg : SwH g) (hh : SwH h) :
    g * h ∈ blocks1408 := by
  intro i
  rw [Equiv.Perm.mul_apply]
  have a := hg (h i)
  have b := hh i
  tauto

theorem mem_mul_swH {g h : Equiv.Perm (Fin 1408)} (hg : g ∈ blocks1408) (hh : SwH h) :
    SwH (g * h) := by
  intro i
  rw [Equiv.Perm.mul_apply]
  have a : (g (h i)).val < 704 ↔ (h i).val < 704 := hg (h i)
  have b := hh i
  tauto

theorem swH_mul_mem {g h : Equiv.Perm (Fin 1408)} (hg : SwH g) (hh : h ∈ blocks1408) :
    SwH (g * h) := by
  intro i
  rw [Equiv.Perm.mul_apply]
  have a := hg (h i)
  have b : (h i).val < 704 ↔ i.val < 704 := hh i
  tauto

theorem swH_inv {g : Equiv.Perm (Fin 1408)} (hg : SwH g) : SwH g⁻¹ := by
  intro i
  have a := hg (g⁻¹ i)
  have e : g (g⁻¹ i) = i := by simp
  rw [e] at a
  tauto

def presSw : Subgroup (Equiv.Perm (Fin 1408)) where
  carrier := {g | g ∈ blocks1408 ∨ SwH g}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · exact Or.inl (mul_mem hg hh)
    · exact Or.inr (mem_mul_swH hg hh)
    · exact Or.inr (swH_mul_mem hg hh)
    · exact Or.inl (swH_mul_swH hg hh)
  inv_mem' := by
    rintro g (hg | hg)
    · exact Or.inl (inv_mem hg)
    · exact Or.inr (swH_inv hg)

theorem half_parts : (∀ l < 3, halvesK (kK l) = true) ∧
    (∀ l < 3, halvesK (WK (tGens.getD l [])) = true) ∧ halvesK (uK 0) = true ∧
    swapsK (uK 1) = true ∧ swapsK (specK uK (nSpec1.getD 3 [])) = true := by
  have h := ch26773_half
  simp only [bAnd_iff] at h
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨fun l hl => allN_spec a l hl, fun l hl => allN_spec b l hl, c, d, e⟩

theorem repU (l : Nat) (hl : l < 2) : RepC (uK l) (elemW (classz.centGens.getD l [])) :=
  repC_word (gen_letters hl)

theorem u2_swH : SwH (elemW (classz.centGens.getD 1 [])) :=
  swap_of (repU 1 (by norm_num)) half_parts.2.2.2.1

theorem czC_le : czC ≤ presSw := by
  rw [closure_le]
  refine of_gens (k := 2) (by decide) fun j hj => ?_
  match j, hj with
  | 0, _ => exact Or.inl (pres_of (repU 0 (by norm_num)) half_parts.2.2.1)
  | 1, _ => exact Or.inr u2_swH

theorem czC_dich {g : Equiv.Perm (Fin 1408)} (hg : g ∈ czC) : g ∈ blocks1408 ∨ SwH g :=
  czC_le hg

theorem u2_mem : elemW (classz.centGens.getD 1 []) ∈ czC := elemW_getD_mem _ 1

theorem card_K' (hP : Nat.card ↥P1408 = 177408000) : Nat.card ↥(czC ⊓ blocks1408) = 15360 := by
  have hidx : (blocks1408.subgroupOf czC).index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨_, u2_mem⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases czC_le b.2 with hb | hb
    · exact Or.inr ⟨hb, not_mem_of_swH (mem_mul_swH hb u2_swH)⟩
    · exact Or.inl ⟨swH_mul_swH hb u2_swH, not_mem_of_swH hb⟩
  have hc := Subgroup.card_mul_index (blocks1408.subgroupOf czC)
  rw [hidx, (czT_eq hP).2] at hc
  have e := Subgroup.card_map_of_injective (K := blocks1408.subgroupOf czC) (f := czC.subtype)
    (Subgroup.subtype_injective czC)
  rw [Subgroup.subgroupOf_map_subtype, inf_comm] at e
  omega

theorem n_mem : elemW (specWord classz.centGens (nSpec1.getD 3 [])) ∈ czC :=
  elemW_specWord_mem _ _

theorem repN : RepC (specK uK (nSpec1.getD 3 []))
    (elemW (specWord classz.centGens (nSpec1.getD 3 []))) := by
  rw [specK_eq lU uK_eq]
  exact repC_word (lettersOK_specWord lU _)

theorem n_swH : SwH (elemW (specWord classz.centGens (nSpec1.getD 3 []))) :=
  swap_of repN half_parts.2.2.2.2

theorem n_triv : ∀ p : Fin 1408,
    blkF 5 blkData1.blk (elemW (specWord classz.centGens (nSpec1.getD 3 [])) p) =
      blkF 5 blkData1.blk p := by
  have h := tI1
  simp only [tableI1OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, htriv⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hw : specWord classz.centGens (nSpec1.getD 3 []) ∈ nWords1 := by
    change _ ∈ nSpec1.map (specWord classz.centGens)
    exact List.mem_map.2 ⟨_, (by decide : nSpec1.getD 3 [] ∈ nSpec1), rfl⟩
  exact blkTrivOK_spec (repWM (lettersOK_specWord lU _)) (List.all_eq_true.1 htriv _ hw)

theorem blkC : ∃ φ : ↥czC →* Equiv.Perm (Fin 5), Nat.card ↥φ.range = 120 ∧
    ∀ x : ↥czC, φ x = 1 ↔
      ∀ p : Fin 1408, blkF 5 blkData1.blk ((x : Equiv.Perm (Fin 1408)) p) = blkF 5 blkData1.blk p := by
  obtain ⟨φ, -, hr, hk⟩ := blkData_spec dat1
  have h2 : Nat.card ↥φ.range = 120 := by
    rw [hr]
    exact blkImage_spec dat1 (by change 5 < 2 ^ 32; norm_num) img1
  exact ⟨φ, h2, hk⟩

end CFSG.KD.HN1408.TK

end
