module

public import Certificates.Kernel.Sporadic.OddCore.Suz10741
public import Certificates.Kernel.Sporadic.OddCore.Suz26990F
import CFSG.Certificates.Kernel.SetOrbSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34KSnd
open CFSG.EvenSporadicStandard.Solomon78 CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

theorem pts_lt {i : Nat} (hi : i < 42) : suzL34Pts[i]! < 1782 := by
  have h := k10741P
  simp only [suzL34PtsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.1.1.2 i hi

theorem tab_lt {T : Array Nat} (hT : T = l10741TA ∨ T = l10741TB) {i : Nat} (hi : i < 42) :
    T[i]! < 42 := by
  have h := k10741P
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rcases hT with rfl | rfl
  · exact (h.2 i hi).1
  · exact (h.2 i hi).2

theorem index_pts {j : Nat} (hj : j < 42) : suzL34Index suzL34Pts[j]! = j := by
  have h := List.all_eq_true.1 k10741I j (List.mem_range.2 hj)
  simpa using h

theorem restr_get {P : Nat} {T : Array Nat} (h : restrK P T = true) {i : Nat} (hi : i < 42) :
    (unpack 1782 11 P)[suzL34Pts[i]!]! = suzL34Pts[T[i]!]! := by
  rw [CFSG.KC.SetOrb.unpack_get (pts_lt hi)]
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h i (List.mem_range.2 hi))

theorem restrOK_of {P : Nat} {T : Array Nat} (hT : T = l10741TA ∨ T = l10741TB)
    (h : restrK P T = true) : suzL34RestrOK T (unpack 1782 11 P) = true := by
  unfold suzL34RestrOK
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [restr_get h hi']
  simp [tab_lt hT hi']

theorem tab_of {P : Nat} {T : Array Nat} (hT : T = l10741TA ∨ T = l10741TB) (hs : T.size = 42)
    (h : restrK P T = true) :
    (Array.ofFn (n := 42) fun i => suzL34Index ((unpack 1782 11 P)[suzL34Pts[i.val]!]!)) = T := by
  refine Array.ext (by rw [Array.size_ofFn, hs]) fun i h1 h2 => ?_
  have hi : i < 42 := by simpa using h1
  rw [Array.getElem_ofFn, restr_get h hi, index_pts (tab_lt hT hi), getElem!_pos T i h2]

theorem parts : restrK PA l10741TA = true ∧ restrK PB l10741TB = true := by
  have h := k10741
  rw [strictB_app, strictB_app] at h
  exact andB_iff.1 h

theorem ta_eq : suzL34TA = l10741TA := by
  unfold suzL34TA
  rw [pa_eq]
  exact tab_of (Or.inl rfl) rfl parts.1

theorem tb_eq : suzL34TB = l10741TB := by
  unfold suzL34TB
  rw [pb_eq]
  exact tab_of (Or.inr rfl) rfl parts.2

theorem check10741 : suzL34Check = true := by
  have hP : suzL34PtsOK = true := by
    have h := k10741P
    simp only [Bool.and_eq_true] at h
    exact h.1
  have hW := k10741W
  unfold l10741WordTab at hW
  unfold suzL34Check suzL34WordsOK suzL34WordTab suzL34GenTab
  rw [ta_eq, tb_eq, pa_eq, pb_eq, hP, restrOK_of (Or.inl rfl) parts.1,
    restrOK_of (Or.inr rfl) parts.2, hW]
  rfl

end CertificateChecks.KernelSpor.S26990

end
