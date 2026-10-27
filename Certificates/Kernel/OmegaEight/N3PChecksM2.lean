module

public import Certificates.Kernel.OmegaEight.N3PW
public import Certificates.Kernel.OmegaEight.PlusNodeData
public import CFSG.Certificates.Kernel.O8NodeSound
public import CFSG.Certificates.Kernel.O8N3Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

@[expose] noncomputable def invN3P : List ℕ :=
  ((List.range EnN3PT.m).map (enKey EnN3PT.D)).filter fun k => k != ID12 && mul12K k k == ID12

theorem invsOf_wN3P : invsOf wN3P.tcE.keys = invN3P := by
  simp only [invsOf, wN3P, decE_toList, mulK_eq, idK_eq, invN3P]

theorem sw_eqN3P : PnSW = swarK := by
  have h : (PnSW == swarK) = true := by quickRfl
  exact eq_of_beq h

set_option maxHeartbeats 0 in
theorem m2_okN3P : m2Check wN3P = true := by
  have hb : ∀ v < 4096, (fixMaskW swarK phiK).testBit v = (mulVecK phiK v == v) := fun v hv => by
    rw [testBit_fixMaskW _ hv, mulVecK_eq]
  rw [m2Check, allRootsF_eq (base := (List.range 4096).filter fun v => mulVecK phiK v == v)
      (fun v hv => List.mem_range.1 (List.mem_filter.1 hv).1),
    invsOf_wN3P, allRoots_eqM sw_eqN3P (fixMaskW_lt _) hb, ← sw_eqN3P, all_eq_range]
  refine all_range_of_blocks (s := 0) (nb := 256) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

set_option maxHeartbeats 0 in
theorem off_okN3P : offCheck wN3P = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  rw [offCheck, allRootsF_eq (base := List.range 4096) (fun v hv => List.mem_range.1 hv),
    invsOf_wN3P, hr,
    allRoots_eqM sw_eqN3P (Nat.sub_one_lt (by positivity)) hb, all_eq_range]
  refine all_range_of_blocks (s := 0) (nb := 256) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

set_option maxHeartbeats 0 in
theorem no_okN3P : noChk wN3P = true := by
  simp only [noChk, wN3P, ← Array.all_toList, decE_toList, List.all_map, fpowK_eq, idK_eq]
  refine all_range_of_blocks (s := 12) (nb := 20) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
