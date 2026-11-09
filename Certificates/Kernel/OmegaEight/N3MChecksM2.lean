module

public import Certificates.Kernel.OmegaEight.N3MW
public import Certificates.Kernel.OmegaEight.PlusNodeData
public import Certificates.Kernel.OmegaEight.PnSWEq
public import CFSG.Certificates.Kernel.O8NodeSound
public import CFSG.Certificates.Kernel.O8N3Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

@[expose] noncomputable def invN3M : List ℕ :=
  ((List.range EnN3MT.m).map (enKey EnN3MT.D)).filter fun k => k != ID12 && mul12K k k == ID12

theorem invsOf_wN3M : invsOf wN3M.tcE.keys = invN3M := by
  simp only [invsOf, wN3M, decE_toList, mulK_eq, idK_eq, invN3M]

theorem invN3M_length : invN3M.length = 87 := by decide +kernel

set_option maxHeartbeats 0 in
theorem m2_okN3M : m2Check wN3M = true := by
  have hb : ∀ v < 4096, (fixMaskW swarK phiK).testBit v = (mulVecK phiK v == v) := fun v hv => by
    rw [testBit_fixMaskW _ hv, mulVecK_eq]
  rw [m2Check, allRootsMinF_eq (base := (List.range 4096).filter fun v => mulVecK phiK v == v)
      (fun v hv => List.mem_range.1 (List.mem_filter.1 hv).1), invsOf_wN3M, allRootsMin]
  simp only [commAbove, mulK_eq, rootCheck_eqM_proved PnSW_eq hb]
  rw [← PnSW_eq]
  refine all_of_getD invN3M_length fun i hi => ?_
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem off_okN3M : offCheck wN3M = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  rw [offCheck, allRootsMinF_eq (base := List.range 4096) (fun v hv => List.mem_range.1 hv),
    invsOf_wN3M, allRootsMin, hr]
  simp only [commAbove, mulK_eq, rootCheck_eqM_proved PnSW_eq hb]
  refine all_of_getD invN3M_length fun i hi => ?_
  interval_cases i <;> decide +kernel

theorem no7_of_card {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true)
    (hc : Nat.gcd 7 E.keys.size = 1) :
    (E.keys.all fun c => fpowK c 7 != idK || c == idK) = true := by
  rw [Array.all_eq_true]
  intro i hi
  obtain ⟨x, hx, hr⟩ := Enum.exists_mem hE i hi
  have hk : E.keys[i] = E.keys.getD i 0 := by
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [hk]
  by_cases h : fpowK (E.keys.getD i 0) 7 = idK
  · have h7 := hr.fpow (n := 7) (by norm_num)
    rw [h] at h7
    have hp : x ^ 7 = 1 := h7.unique rep_one
    have hd := Subgroup.orderOf_dvd_natCard _ hx
    rw [Enum.card_eq hE] at hd
    have ho := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp) hd
    rw [hc, Nat.dvd_one, orderOf_eq_one_iff] at ho
    have hr1 : Rep idK x := by
      rw [ho]
      exact rep_one
    rw [hr.key_unique hr1 (Enum.key_lt hE hi) idK_lt, Bool.or_eq_true, beq_iff_eq]
    exact Or.inr rfl
  · rw [Bool.or_eq_true, bne_iff_ne]
    exact Or.inl h

theorem no_okN3M : noChk wN3M = true := by
  rw [noChk]
  refine no7_of_card cE_okN3M ?_
  simp only [wN3M, decE_keys_size]
  decide +kernel

end CertificateChecks.KernelO8
