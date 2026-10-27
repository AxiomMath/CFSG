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

set_option maxHeartbeats 0 in
theorem m2_okN3M : m2Check wN3M = true := by
  have hb : ∀ v < 4096, (fixMaskW swarK phiK).testBit v = (mulVecK phiK v == v) := fun v hv => by
    rw [testBit_fixMaskW _ hv, mulVecK_eq]
  rw [m2Check, allRootsF_eq (base := (List.range 4096).filter fun v => mulVecK phiK v == v)
      (fun v hv => List.mem_range.1 (List.mem_filter.1 hv).1),
    invsOf_wN3M, allRoots_eqM PnSW_eq (fixMaskW_lt _) hb, ← PnSW_eq, all_eq_range]
  refine all_range_of_blocks (s := 0) (nb := 256) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

set_option maxHeartbeats 0 in
theorem off_okN3M : offCheck wN3M = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  rw [offCheck, allRootsF_eq (base := List.range 4096) (fun v hv => List.mem_range.1 hv),
    invsOf_wN3M, hr,
    allRoots_eqM PnSW_eq (Nat.sub_one_lt (by positivity)) hb, all_eq_range]
  refine all_range_of_blocks (s := 0) (nb := 256) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

set_option maxHeartbeats 0 in
theorem no_okN3M : noChk wN3M = true := by
  simp only [noChk, wN3M, ← Array.all_toList, decE_toList, List.all_map, fpowK_eq, idK_eq]
  refine all_range_of_blocks (s := 12) (nb := 26) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
