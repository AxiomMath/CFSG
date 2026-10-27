module

public import Certificates.Kernel.OmegaEight.PlusW
public import Certificates.Kernel.OmegaEight.PlusNodeData
public import CFSG.Certificates.Kernel.O8NodeSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.O8PlusSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

@[expose] noncomputable def invTP : List ℕ :=
  ((List.range EnTP.m).map (enKey EnTP.D)).filter fun k => k != ID12 && mul12K k k == ID12

theorem invsOf_wP : invsOf wP.tcE.keys = invTP := by
  simp only [invsOf, wP, decE_toList, mulK_eq, idK_eq, invTP]

theorem sw_eq : PnSW = swarK := by
  have h : (PnSW == swarK) = true := by quickRfl
  exact eq_of_beq h

theorem invTP_length : invTP.length = 55 := by
  decide +kernel

theorem all_invTP {f : ℕ → Bool} (h : ∀ i < 55, f (invTP.getD i 0) = true) :
    invTP.all f = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have := h i (invTP_length ▸ hi)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

set_option maxHeartbeats 0 in
theorem m2_okP : m2Check wP = true := by
  have hb : ∀ v < 4096, (fixMaskW swarK phiK).testBit v = (mulVecK phiK v == v) := fun v hv => by
    rw [testBit_fixMaskW _ hv, mulVecK_eq]
  rw [m2Check, invsOf_wP, allRoots_eqM sw_eq (fixMaskW_lt _) hb, ← sw_eq]
  refine all_invTP fun i hi => ?_
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem off_okP : offCheck wP = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  rw [offCheck, invsOf_wP, hr, allRoots_eqM sw_eq (Nat.sub_one_lt (by positivity)) hb]
  refine all_invTP fun i hi => ?_
  interval_cases i <;> decide +kernel

end CertificateChecks.KernelO8
