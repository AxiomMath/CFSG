module

public import Certificates.Kernel.Sporadic.OddCore.J2EA
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.J2EA

open CFSG.SeitzReduction.SporadicRefine

theorem cl1 : closedK j2EAIdxOne = true := by quickRfl
theorem cl2 : closedK j2EAIdxTwo = true := by quickRfl

theorem ct0 : (List.range' 0 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct1 : (List.range' 32 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct2 : (List.range' 64 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct3 : (List.range' 96 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct4 : (List.range' 128 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct5 : (List.range' 160 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct6 : (List.range' 192 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem ct7 : (List.range' 224 32).all (countAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl

theorem sp0 : (List.range' 0 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp1 : (List.range' 32 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp2 : (List.range' 64 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp3 : (List.range' 96 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp4 : (List.range' 128 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp5 : (List.range' 160 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp6 : (List.range' 192 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl
theorem sp7 : (List.range' 224 32).all (suppAt j2EAIdxOne j2EAIdxTwo) = true := by quickRfl

theorem of_blocks {f : Nat → Bool} (b0 : (List.range' 0 32).all f = true)
    (b1 : (List.range' 32 32).all f = true) (b2 : (List.range' 64 32).all f = true)
    (b3 : (List.range' 96 32).all f = true) (b4 : (List.range' 128 32).all f = true)
    (b5 : (List.range' 160 32).all f = true) (b6 : (List.range' 192 32).all f = true)
    (b7 : (List.range' 224 32).all f = true) : (List.range 256).all f = true := by
  have hb : ∀ k < 8, (List.range' (32 * k) 32).all f = true := fun k hk => by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
    exacts [b0, b1, b2, b3, b4, b5, b6, b7, absurd hk (by omega)]
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_range] at hx
  refine List.all_eq_true.1 (hb (x / 32) (by omega)) x ?_
  rw [List.mem_range'_1]
  omega

theorem idx1 : ∀ y ∈ j2EAIdxOne, y < 256 := by decide
theorem idx2 : ∀ y ∈ j2EAIdxTwo, y < 256 := by decide

theorem cert3966 : (idxClosedOK 315 j2SylEnum j2EAIdxOne = true) ∧
    (idxClosedOK 315 j2SylEnum j2EAIdxTwo = true) ∧
    (eaCountOK 315 CFSG.Sporadic.SmallOddCore.j2Sift j2SylEnum j2EAIdxOne j2EAIdxTwo = true) ∧
    (eaSupportOK 315 CFSG.Sporadic.SmallOddCore.j2Sift j2SylEnum j2EAIdxOne j2EAIdxTwo = true) :=
  ⟨(closed_eq idx1).trans cl1, (closed_eq idx2).trans cl2,
    (count_eq _ _).trans (of_blocks ct0 ct1 ct2 ct3 ct4 ct5 ct6 ct7),
    (supp_eq idx1 idx2).trans (of_blocks sp0 sp1 sp2 sp3 sp4 sp5 sp6 sp7)⟩

end CertificateChecks.KernelSpor.J2EA

end
