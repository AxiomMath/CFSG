module

public import Certificates.Data.Kernel.PermCent.KGrpC2
public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.GH74.KGroups.M11Inputs
public import CFSG.Certificates.Kernel.PermCent.KGrpOddConjSound
public import Certificates.Data.Kernel.PermCent.KGrpC
import Certificates.Kernel.Misc.KGroups.M11Valid

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5097

open CFSG.GH74.KGroups.M11 CFSG.Certificates CFSG.Sporadic.Schreier

theorem conj_one_class {n : Nat} [Small n] (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (a : CV n) (k : Nat) (hk : (elemsC Q).length = k * (centL (elemsC Q) a).length)
    (hI : ((elemsC Q).filter invOC).length = k) (haQ : a ∈ elemsC Q) (hai : invOC a = true) :
    ∀ τ ∈ (elemsC Q).filter invOC, ∃ r ∈ [a], ∃ g ∈ elemsC Q, τ = g * r * g⁻¹ := by
  set I := (elemsC Q).filter invOC with hIdef
  have hInd : I.Nodup := (nodup_elemsC Q hQ).filter _
  set Ca := ((elemsC Q).map fun g => g * a * g⁻¹).toFinset with hCa
  have hpos : 0 < (centL (elemsC Q) a).length :=
    List.length_pos_of_mem ((mem_centL _ a 1).2 ⟨one_memC Q hQ, by group⟩)
  have hcard : Ca.card = k :=
    Nat.eq_of_mul_eq_mul_right hpos ((card_conj_mul Q hQ a).trans hk)
  have hsub : Ca ⊆ I.toFinset := by
    intro y hy
    rw [hCa, List.mem_toFinset, List.mem_map] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [List.mem_toFinset, hIdef, List.mem_filter, invOC_conj]
    exact ⟨conj_mem_elemsC Q hQ hg haQ, hai⟩
  have hU : Ca = I.toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [List.toFinset_card_of_nodup hInd, hI, hcard]
  intro τ hτ
  have h : τ ∈ Ca := by rw [hU, List.mem_toFinset]; exact hτ
  rw [hCa, List.mem_toFinset, List.mem_map] at h
  obtain ⟨g, hg, e⟩ := h
  exact ⟨a, by simp, g, hg, e.symm⟩

@[expose] noncomputable def tK : CV 11 := ((elemsC Q).filter invOC).headD 1

theorem kMemI : tK ∈ (elemsC Q).filter invOC := by decide +kernel

theorem kCnt1 : (elemsC Q).length = 165 * (centL (elemsC Q) tK).length := by decide +kernel

theorem kCnt2 : ((elemsC Q).filter invOC).length = 165 := by decide +kernel

theorem kOdd : oddCoreAtC 495 (centL (elemsC Q) tK) (centL (elemsC Q) tK) = true := by
  decide +kernel

theorem k5097 : oddCoreCheckC 495 (elemsC Q) (elemsC Q) = true := by
  have hQ : ValidSchreier Q := CertificateChecks.KernelMisc.M11C.valid
  have hm := List.mem_filter.1 kMemI
  refine oddCoreCheckC_of_reps Q Q hQ hQ le_rfl 495 [tK]
    (conj_one_class Q hQ tK 165 kCnt1 kCnt2 hm.1 hm.2) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact kOdd

end CFSG.Certificates.Kernel.PkCV.KGrp.K5097
