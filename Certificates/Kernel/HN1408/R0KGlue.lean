module

public import Certificates.Kernel.HN1408.R0KFacts
public import Certificates.Kernel.HN1408.AKGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Coe
public import Certificates.Certificate441665Base

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.R0K

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.EvenSporadicStandard.HNRecog.HaradaLA
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KD.HN1408
open CFSG.KD.HN1408.CzT CFSG.KD.HN1408.AK

theorem coe_pmem {c : ↥P1408} (hc : c ∈ centralizer ({pZ} : Set ↥P1408)) :
    (c : Equiv.Perm (Fin 1408)) ∈ Cz :=
  mem_inf.2 ⟨c.2, Subgroup.mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_P.1 hc)⟩

theorem pmem_of {c : ↥P1408} (hc : (c : Equiv.Perm (Fin 1408)) ∈ Cz) :
    c ∈ centralizer ({pZ} : Set ↥P1408) :=
  mem_centralizer_singleton_P.2 (Subgroup.mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2)

theorem pZ_sq : pZ * pZ = 1 :=
  Subtype.ext (by rw [Subgroup.coe_mul, coe_pZ, ← u0_eq]; exact u_sq (by norm_num))

theorem mem_zp {y : ↥P1408} : y ∈ zpowers pZ ↔ y = 1 ∨ y = pZ := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hi : pZ⁻¹ = pZ := inv_eq_of_mul_eq_one_right pZ_sq
    clear hy
    induction k using Int.induction_on
    · exact Or.inl (zpow_zero _)
    · rename_i n ih
      rw [zpow_add_one]
      rcases ih with h | h
      · right
        rw [h, one_mul]
      · left
        rw [h, pZ_sq]
    · rename_i n ih
      rw [zpow_sub_one, hi]
      rcases ih with h | h
      · right
        rw [h, one_mul]
      · left
        rw [h, pZ_sq]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem bil_iff (k : Nat) : bilC k 1 = 0 ↔ bil (vecOfCode k) (Pi.single 0 1) = 0 := by
  have hbil : (bilC k 1 : ZMod 2) = bil (vecOfCode k) (Pi.single 0 1) := by
    rw [bilC_spec k 1, vecOfCode_one]
  have hlt2 : bilC k 1 < 2 := Nat.mod_lt _ (by norm_num)
  rw [← hbil]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff (bilC k 1) 2).1 h) hlt2

theorem eta_mem {u : Nat} (hu : u < 64) (he : etaB u = true) : u ∈ etaCodes := by
  unfold etaB at he
  obtain ⟨a, b⟩ := mkA he
  unfold etaCodes
  rw [List.mem_filter]
  refine ⟨List.mem_range.2 hu, ?_⟩
  rw [Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b]
  rfl

theorem eta_of {u : Nat} (h : u ∈ etaCodes) : etaB u = true := by
  unfold etaCodes at h
  rw [List.mem_filter] at h
  have h2 := h.2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  unfold etaB
  rw [h2.1, h2.2]
  rfl

theorem r0FactsK (hP : Nat.card ↥P1408 = 177408000) : Certificates.R0Facts where
  r0_card := (card_wordSubgroupP nWords1).trans r0_card
  r0_le_centralizer _ hx := pmem_of (r0_le hx)
  r0_normal c hc x hx := by
    rw [mem_wordSubgroupP]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact r0_normal hP (coe_pmem hc) hx
  r0_sq x hx := by
    rw [mem_zp]
    rcases r0_sq hP (mem_wordSubgroupP.1 hx) with h | h
    · left
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two, h, Subgroup.coe_one]
    · right
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two, h, coe_pZ]
  r0_inter v := by
    rw [mem_wordSubgroupP, ← vecOfCode_codeOfVec v, coe_iota, inter_iff hP (codeOfVec_lt v),
      bil_iff]
  r0_eichler r hr := by
    obtain ⟨u, hu, he, hrel⟩ := eich_ex hP (mem_wordSubgroupP.1 hr)
    have hum : u ∈ etaCodes := eta_mem hu he
    obtain ⟨-, hb, hl⟩ := (mem_etaCodes_iff u).1 hum
    refine ⟨vecOfCode u, hb, hl, fun x => Subtype.ext ?_⟩
    have hk := codeOfVec_lt x
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← vecOfCode_codeOfVec x, ← eichC_spec hum hk, coe_iota, coe_iota, hrel _ hk,
      mul_inv_cancel_right]
  r0_surj u hb hl := by
    have hu := codeOfVec_lt u
    have hum : codeOfVec u ∈ etaCodes := (mem_etaCodes_iff _).2
      ⟨hu, by rw [vecOfCode_codeOfVec]; exact hb, by rw [vecOfCode_codeOfVec]; exact hl⟩
    obtain ⟨r, hr, hrel⟩ := surj_ex hP hu (eta_of hum)
    refine ⟨⟨r, wordSubgroup_le nWords1 hr⟩, mem_wordSubgroupP.2 hr, fun x => Subtype.ext ?_⟩
    have hk := codeOfVec_lt x
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e := eichC_spec hum hk
    rw [vecOfCode_codeOfVec, vecOfCode_codeOfVec] at e
    rw [← e, ← vecOfCode_codeOfVec x, coe_iota, coe_iota, vecOfCode_codeOfVec, hrel _ hk,
      mul_inv_cancel_right]
  r0_faith c hc h := by
    refine faith hP (coe_pmem hc) fun j hj => ?_
    have hz := h ⟨_, elemW_mem (nWords1.getD j [])⟩ (genX_mem hj)
    rcases mem_zp.1 hz with h1 | h1
    · left
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)
    · right
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_pZ] at h2
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_iff_eq_mul.1 h2)
  f_le_centralizer _ hx :=
    mem_centralizer_singleton_P.2 (Subgroup.mem_centralizer_singleton_iff.1 (mem_inf.1 (f_le hx)).2)
  f_iso := by
    obtain ⟨e⟩ := nonempty_mulEquiv_of_cayleyOK f_cay card_target_A5
    exact ⟨(Subgroup.subgroupOfEquivOfLe (wordSubgroup_le fWords)).trans e⟩

end CFSG.KD.HN1408.R0K

end
