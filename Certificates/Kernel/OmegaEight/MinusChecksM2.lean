module

public import Certificates.Kernel.OmegaEight.MinusW
public import Certificates.Kernel.OmegaEight.PlusNodeData
public import CFSG.Certificates.Kernel.O8NodeSound
public import CFSG.Certificates.Kernel.O8MinusSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

@[expose] noncomputable def invTM : List ℕ :=
  ((List.range EnTM.m).map (enKey EnTM.D)).filter fun k => k != ID12 && mul12K k k == ID12

theorem invsOf_wM : invsOf wM.tcE.keys = invTM := by
  simp only [invsOf, wM, decE_toList, mulK_eq, idK_eq, invTM]

theorem sw_eqM2 : PnSW = swarK := by
  have h : (PnSW == swarK) = true := by quickRfl
  exact eq_of_beq h

set_option maxHeartbeats 0 in
theorem m2_okM : m2Check wM = true := by
  have hb : ∀ v < 4096, (fixMaskW swarK phiK).testBit v = (mulVecK phiK v == v) := fun v hv => by
    rw [testBit_fixMaskW _ hv, mulVecK_eq]
  have hl : invTM.length = 55 := by decide +kernel
  rw [m2Check, invsOf_wM, allRoots_eqM sw_eqM2 (fixMaskW_lt _) hb, ← sw_eqM2]
  refine all_of_getD hl fun i hi => ?_
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem off_okM : offCheck wM = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  have hl : invTM.length = 55 := by decide +kernel
  rw [offCheck, invsOf_wM, hr, allRoots_eqM sw_eqM2 (Nat.sub_one_lt (by positivity)) hb]
  refine all_of_getD hl fun i hi => ?_
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem no8_okM : no8Chk wM = true := by
  simp only [no8Chk, no8Check, wM, ← Array.all_toList, decE_toList, List.all_map, fpowK_eq,
    idK_eq]
  refine all_range_of_blocks (s := 12) (nb := 13) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
