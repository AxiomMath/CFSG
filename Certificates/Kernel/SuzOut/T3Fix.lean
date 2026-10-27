module

public import Certificates.Kernel.SuzOut.T3Check
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzOut.T3

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.SuzOddCore CertificateChecks.KernelSpor

@[expose] noncomputable def fixL3 : List Nat :=
  (List.range 1782).filter fun p => Nat.beq (pg 11 (mask 11) (SuzTP 3) p) p

theorem fixL3_eq : fixL3 = fixL := by decide +kernel

private theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem fixList_eq3 : fixList 3 = fixL := by
  rw [← fixL3_eq]
  unfold fixList fixL3 fixedList
  rw [(CertificateChecks.KernelSpor.OddCore.rep_facts (i := 3) (by decide)).1]
  refine List.filter_congr fun p hp => ?_
  rw [CFSG.KC.BfsPin.unpack_get' (List.mem_range.1 hp), beq_nat]

theorem fixL_lt : ∀ x ∈ fixL, x < 1782 := by
  rw [← fixL3_eq]
  exact fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1

theorem fixL_length : fixL.length = 100 := by simp [fixL]

end CertificateChecks.KernelSuzOut.T3

end
