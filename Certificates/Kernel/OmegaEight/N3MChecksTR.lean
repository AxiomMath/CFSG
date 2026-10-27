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

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

@[expose] noncomputable def invN3M3 : List ℕ :=
  ((List.range EnN3MS3.m).map (enKey EnN3MS3.D)).filter fun k => k != ID12 && mul12K k k == ID12

theorem invsOf_wN3M3 : invsOf wN3M.sE3.keys = invN3M3 := by
  simp only [invsOf, wN3M, decE_toList, mulK_eq, idK_eq, invN3M3]

set_option maxHeartbeats 0 in
theorem third_roots_okN3M :
    allRootsF 2048 (invsOf wN3M.sE3.keys) (List.range 4096) = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  rw [allRootsF_eq (base := List.range 4096) (fun v hv => List.mem_range.1 hv),
    invsOf_wN3M3, hr, allRoots_eqM PnSW_eq (Nat.sub_one_lt (by positivity)) hb, all_eq_range]
  refine all_range_of_blocks (s := 0) (nb := 512) (by decide +kernel) fun b hb => ?_
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
