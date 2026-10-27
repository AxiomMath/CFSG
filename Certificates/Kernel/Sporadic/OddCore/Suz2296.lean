module

public import Certificates.Kernel.Sporadic.OddCore.SuzInvOdd
public import Certificates.Kernel.Sporadic.OddCore.SuzFusion
public import Certificates.Kernel.Sporadic.OddCore.Suz2289
public import CFSG.Certificates.Kernel.Spor.LenSound
public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
import all CFSG.Sporadic.SuzOddCore.InvArrays
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Enum
open CFSG.KS CFSG.KS.Len

theorem lens2296 : bAnd(Nat.beq (lenK SuzInvT0.chars) 491833,
    bAnd(Nat.beq (lenK SuzInvT1.chars) 379567, bAnd(Nat.beq (lenK SuzInvT2.chars) 213841,
    bAnd(Nat.beq (lenK SuzInvT3.chars) 331453, Nat.beq (lenK SuzFusT.chars) 283339)))) = true := by
  quickRfl

set_option maxHeartbeats 2000000 in
theorem derivs2296 : ∀ i < 4, derivsOK (invFullGenCounts.getD i 0) (invFullDerivs i) = true ∧
      derivsOK (invInnerGenCounts.getD i 0) (invInnerDerivs i) = true ∧
      (invFullDerivs i).size = invFullStrongCounts.getD i 0 ∧
      (invInnerDerivs i).size = invInnerStrongCounts.getD i 0 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem nbrs2296 : invNeighbors.length = 416 ∧ strictIncr invNeighbors = true ∧
    (∀ x ∈ invNeighbors, 0 < x ∧ x < 1782) := by
  decide +kernel

theorem textLen {s : String} {cs : List Char} {m : Nat} (hs : s = String.ofList cs)
    (h : Nat.beq (lenK cs) m = true) : s.length = m := by
  rw [hs, String.length_ofList, ← lenK_eq, Nat.eq_of_beq_eq_true h]

theorem facts2296 :
    (∀ i < 4, (invText i).length = 5346 * invRunCount i + 1) ∧
    (∀ i < 4, ∀ k < invRunCount i, permOK 1782 (invRun i k) = true) ∧
    invFusionText.length = 5346 * 53 + 1 ∧ (∀ k < 53, permOK 1782 (invFusionRun k) = true) ∧
    (∀ i < 4, derivsOK (invFullGenCounts.getD i 0) (invFullDerivs i) = true ∧
      derivsOK (invInnerGenCounts.getD i 0) (invInnerDerivs i) = true ∧
      (invFullDerivs i).size = invFullStrongCounts.getD i 0 ∧
      (invInnerDerivs i).size = invInnerStrongCounts.getD i 0) ∧
    invNeighbors.length = 416 ∧ strictIncr invNeighbors = true ∧
    (∀ x ∈ invNeighbors, 0 < x ∧ x < 1782) := by
  obtain ⟨l0, l1, l2, l3, lf⟩ := (by simpa only [bAnd_iff] using lens2296 :
    Nat.beq (lenK SuzInvT0.chars) 491833 = true ∧ Nat.beq (lenK SuzInvT1.chars) 379567 = true ∧
    Nat.beq (lenK SuzInvT2.chars) 213841 = true ∧ Nat.beq (lenK SuzInvT3.chars) 331453 = true ∧
    Nat.beq (lenK SuzFusT.chars) 283339 = true)
  refine ⟨fun i hi => ?_, fun i hi k hk => ?_, ?_, fun k hk => ?_, derivs2296, nbrs2296⟩
  · interval_cases i
    · have e : invText 0 = invCase0Text := rfl
      rw [e, textLen SuzInvT0.eq l0]
      rfl
    · have e : invText 1 = invCase1Text := rfl
      rw [e, textLen SuzInvT1.eq l1]
      rfl
    · have e : invText 2 = invCase2Text := rfl
      rw [e, textLen SuzInvT2.eq l2]
      rfl
    · have e : invText 3 = invCase3Text := rfl
      rw [e, textLen SuzInvT3.eq l3]
      rfl
  · rw [run_all hi hk]
    obtain ⟨r, hr⟩ := perm_all hi hk
    exact permOK_unpack hr
  · rw [textLen SuzFusT.eq lf]
  · rw [fusionRun_eq hk]
    exact permOK_unpack (allN_spec fus_perms k hk)

end CertificateChecks.KernelSpor.OddCore

end
