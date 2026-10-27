module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.HexAtSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SuzOddCore.GraphArraysCheckInputs
meta import CFSG.Sporadic.SuzOddCore.GraphArrays
import all CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzLocT CFSG.Sporadic.SuzOddCore.graphLocalText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzLocT CFSG.Sporadic.SuzOddCore.graphLocalText 4 280 15 1

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def locRunsM : Array (Array Nat) := (List.range 22).toArray.map localRun

meta def locRunsInvM : Array (Array Nat) := locRunsM.map (CFSG.Monster.B.Co2.Native.invCand 280)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzLocR CertificateChecks.KernelSpor.OddCore.locRunsM 9

#kmisc_packarrs CertificateChecks.KernelSpor.SuzLocRI CertificateChecks.KernelSpor.OddCore.locRunsInvM 9

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Misc.HexAt CFSG.Certificates.Native

theorem runs_bound : hexAtK SuzLocT.chars 1120 3 280 9 22 SuzLocR = true := by
  quickRfl

theorem run_perms : allN 22 (fun k =>
    invEqK 280 9 (mask 9) (280 * 9) (SuzLocR k) (SuzLocRI k)) = true := by
  quickRfl

theorem dom_ok : bAnd(allN 279 (fun i =>
      Nat.blt (pg 15 (mask 15) (SuzLocT.F 0) i) (pg 15 (mask 15) (SuzLocT.F 0) (Nat.succ i))),
    allN 280 (fun i => Nat.blt (pg 15 (mask 15) (SuzLocT.F 0) i) 22880)) = true := by
  quickRfl

theorem localRun_eq {k : Nat} (hk : k < 22) : localRun k = unpack 280 9 (SuzLocR k) := by
  have h := hexAt_unpack runs_bound hk
  rw [← SuzLocT.eq] at h
  refine Eq.trans ?_ h
  apply Array.ext
  · simp [localRun]
  · intro x _ _
    simp only [localRun, Array.getElem_ofFn]
    have ex : 1120 + 840 * k + 3 * x = 1120 + 3 * (280 * k + x) := by omega
    rw [ex]

theorem localDomain_eq : localDomain = (unpack 280 15 (SuzLocT.F 0)).toList := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzLocT.all 0 (by decide)
  rw [← SuzLocT.eq] at h
  unfold localDomain
  rw [← h]

theorem strictIncr_of_get : ∀ l : List Nat,
    (∀ i (h : i + 1 < l.length), l[i] < l[i + 1]) → strictIncr l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h 0 (by simp), strictIncr_of_get (b :: l) (fun i hi => ?_)⟩
    have := h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
    simpa using this

theorem domain : localDomain.length = 280 ∧ strictIncr localDomain = true ∧
    ∀ x ∈ localDomain, x < 22880 := by
  obtain ⟨h1, h2⟩ := (by simpa only [bAnd_iff] using dom_ok :
    allN 279 (fun i =>
      Nat.blt (pg 15 (mask 15) (SuzLocT.F 0) i) (pg 15 (mask 15) (SuzLocT.F 0) (Nat.succ i))) = true ∧
    allN 280 (fun i => Nat.blt (pg 15 (mask 15) (SuzLocT.F 0) i) 22880) = true)
  rw [localDomain_eq]
  refine ⟨by rw [Array.length_toList]; simp only [unpack, Array.size_ofFn],
    strictIncr_of_get _ (fun i hi => ?_), fun x hx => ?_⟩
  · simp only [Array.length_toList, Array.size_ofFn, unpack] at hi
    simp only [unpack, Array.getElem_toList, Array.getElem_ofFn]
    exact Eq.mp Nat.blt_eq (allN_spec h1 i (by omega))
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [Array.length_toList, Array.size_ofFn, unpack] at hi
    simp only [unpack, Array.getElem_toList, Array.getElem_ofFn]
    exact Eq.mp Nat.blt_eq (allN_spec h2 i hi)

end CertificateChecks.KernelSpor.OddCore

end
