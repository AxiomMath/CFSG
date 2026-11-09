module

public import Certificates.Data.Kernel.PermCent.P45Twin
public import CFSG.Certificates.Kernel.PermCent.KGrpOddConjSound
import Certificates.Kernel.PermCent.ClassCount
import Certificates.Certificate2012

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.P45T

open CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkCV.KGrp

theorem coverC_of_count (Q : RawSchreierDatum 45) (hQ : ValidSchreier Q)
    (a b : CV 45) (ka kb : Nat) (hka : (elemsC Q).length = ka * (centL (elemsC Q) a).length)
    (hkb : (elemsC Q).length = kb * (centL (elemsC Q) b).length)
    (hI : ((elemsC Q).filter invOC).length = ka + kb) (hne : ka ≠ kb) (ha : a ∈ elemsC Q)
    (hb : b ∈ elemsC Q) (hai : invOC a = true) (hbi : invOC b = true) :
    coverC [a, b] (elemsC Q) = true := by
  have hpos : ∀ r, 0 < (centL (elemsC Q) r).length := fun r =>
    List.length_pos_of_mem ((mem_centL _ r 1).2 ⟨one_memC Q hQ, by group⟩)
  have hcard : ∀ r k, (elemsC Q).length = k * (centL (elemsC Q) r).length →
      ((elemsC Q).map fun g => g * r * g⁻¹).toFinset.card = k := fun r k hk =>
    Nat.eq_of_mul_eq_mul_right (hpos r) ((card_conj_mul Q hQ r).trans hk)
  have hcov := ClassCount.cover_two_classes (elemsC Q) invOC (nodup_elemsC Q hQ)
    (fun _ _ hg hh => mul_memC Q hQ hg hh) (fun _ hg => inv_memC Q hQ hg) invOC_conj a b ka kb
    (hcard a ka hka) (hcard b kb hkb) hI hne ha hb hai hbi
  unfold coverC
  rw [List.all_eq_true]
  intro t ht
  have e : (powOneC t 2 && !decide (t = 1)) = invOC t := rfl
  rw [e]
  cases hti : invOC t
  · rfl
  · obtain ⟨g, hg, hor⟩ := hcov t (List.mem_filter.2 ⟨ht, hti⟩)
    rw [Bool.not_true, Bool.false_or, List.any_eq_true]
    refine ⟨g⁻¹, inv_memC Q hQ hg, ?_⟩
    rw [List.any_eq_true]
    rcases hor with rfl | rfl
    · exact ⟨a, by simp, by rw [eq22C_eq, decide_eq_true_iff]; group⟩
    · exact ⟨b, by simp, by rw [eq22C_eq, decide_eq_true_iff]; group⟩

theorem kN1 : (elemsC QP45).length = 45 * (centL (elemsC QP45) (cOf (Certificates.OmegaT0.z0 ()))).length := by
  decide +kernel

theorem kN2 : (elemsC QP45).length = 270 * (centL (elemsC QP45) (cOf (Certificates.OmegaT0.yB ()))).length := by
  decide +kernel

theorem kN3 : ((elemsC QP45).filter invOC).length = 45 + 270 := by decide +kernel

theorem kN4 : cOf (Certificates.OmegaT0.z0 ()) ∈ (elemsC QP45).filter invOC := by decide +kernel

theorem kN5 : cOf (Certificates.OmegaT0.yB ()) ∈ (elemsC QP45).filter invOC := by decide +kernel

theorem kM1 : decide (cntCentC (elemsC QP45) (cOf (Certificates.OmegaT0.z0 ())) = 576) =
    true := by
  decide +kernel

theorem kM2 : decide (cntCentC (elemsC QP45) (cOf (Certificates.OmegaT0.yB ())) = 96) =
    true := by
  decide +kernel

theorem k442001N : n7C = true := by
  have hQ : ValidSchreier QP45 := Certificates.certificate2012.1.1
  have h4 := List.mem_filter.1 kN4
  have h5 := List.mem_filter.1 kN5
  have hc := coverC_of_count QP45 hQ _ _ 45 270 kN1 kN2 kN3 (by decide) h4.1 h5.1 h4.2 h5.2
  simp only [n7C, hc, kM1, kM2, Bool.true_and, Bool.and_true]
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.P45T
