module

public import Certificates.Kernel.HN1408.Cent3Card

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem wcK_parts {R RT WC : Nat → Nat} (h : wcK R RT WC = true) :
    (∀ i < 5, WC i < 1440) ∧ ttK RT (R (WC 0)) = 1 ∧ ttK RT (R (WC 1)) = 1 ∧
      ttK RT (R (WC 3)) = 1 ∧ ttK RT (R (WC 4)) = 1 ∧ mulEq (WC 0) (WC 1) (WC 2) = true ∧
      base2 (fun p => Nat.beq (ev (WC 2) (ev (WC 3) p)) (ev (WC 4) (ev (WC 3) (ev (WC 2) p)))) =
        true := by
  unfold wcK at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, h⟩ := mkA h
  obtain ⟨e, h⟩ := mkA h
  obtain ⟨f, g⟩ := mkA h
  exact ⟨fun i hi => Nat.blt_eq.mp (allN_spec a i hi), Nat.eq_of_beq_eq_true b,
    Nat.eq_of_beq_eq_true c, Nat.eq_of_beq_eq_true d, Nat.eq_of_beq_eq_true e, f, g⟩

theorem comm_of {G : Type*} [Group G] {e f s : G} (h : e * f = s * f * e) :
    s = e * f * e⁻¹ * f⁻¹ := by
  calc s = s * f * e * e⁻¹ * f⁻¹ := by group
    _ = e * f * e⁻¹ * f⁻¹ := by rw [← h]

variable (hpf : PrimeFacts 3 [fix3]) (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j))
include hpf hnc

theorem w_comm : WCommAt pA pZ pZ₁ (repP fix3) := by
  have hC := hC_of hpf
  obtain ⟨hlt, h0, h1, h3, h4, hm, hb⟩ := wcK_parts ch441603_wc
  have k0 := hlt 0 (by norm_num)
  have k1 := hlt 1 (by norm_num)
  have k2 := hlt 2 (by norm_num)
  have k3 := hlt 3 (by norm_num)
  have k4 := hlt 4 (by norm_num)
  have hW : ∀ {k} (hk : k < 1440), ttK RT (R k) = 1 → elH hk ∈ WsubH pA pZ pZ₁ (repP fix3) :=
    fun hk h => subset_closure (tt_mem hpf hnc hk h)
  have he : elH k0 * elH k1 = elH k2 :=
    Subtype.ext (by rw [Subgroup.coe_mul, elH_val, elH_val, elH_val]; exact el_mul hC k0 k1 k2 hm)
  have heW : elH k2 ∈ WsubH pA pZ pZ₁ (repP fix3) := by
    rw [← he]
    exact mul_mem (hW k0 h0) (hW k1 h1)
  obtain ⟨b0, b1⟩ := base2_parts hb
  have hrel : el (WC 2) * el (WC 3) = el (WC 4) * el (WC 3) * el (WC 2) := by
    refine eq_of_base hC (mul_mem (el_mem k2) (el_mem k3))
      (mul_mem (mul_mem (el_mem k4) (el_mem k3)) (el_mem k2)) (Fin.ext ?_) (Fin.ext ?_)
    · simp only [Equiv.Perm.mul_apply]
      rw [el_apply k3 (by norm_num), el_pt k2 (ev_lt k3 (by norm_num)), el_apply k2 (by norm_num),
        el_apply k3 (ev_lt k2 (by norm_num)), el_pt k4 (ev_lt k3 (ev_lt k2 (by norm_num)))]
      exact Nat.eq_of_beq_eq_true b0
    · simp only [Equiv.Perm.mul_apply]
      rw [el_apply k3 (by norm_num), el_pt k2 (ev_lt k3 (by norm_num)), el_apply k2 (by norm_num),
        el_apply k3 (ev_lt k2 (by norm_num)), el_pt k4 (ev_lt k3 (ev_lt k2 (by norm_num)))]
      exact Nat.eq_of_beq_eq_true b1
  have hs : elH k4 = elH k2 * elH k3 * (elH k2)⁻¹ * (elH k3)⁻¹ := by
    refine comm_of (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, elH_val]
    exact hrel
  obtain ⟨hc, hs2, hs1, hst⟩ := tt_mem hpf hnc k4 h4
  refine ⟨elH k4, hc, hs2, hs1, hst, ?_⟩
  rw [hs]
  exact commutator_mem_commutator heW (hW k3 h3)

end CFSG.KD.HN1408.Cent3

end
