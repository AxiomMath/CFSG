module

public import Certificates.Kernel.LocalComp.TwistedE6TwoSound
public import Certificates.Kernel.Misc.E6SlpGens
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.TwistedE6Two

open CFSG.KC.Misc CFSG.KC.Misc.E6Std CFSG.KC.TwistedE6Two
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
open CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

#e6_slp_gens TE progY nGens

theorem kG : gensOK bracketCodes formBits rhoIdx TE.V 0 = true := by quickRfl

theorem kF : factorK TE.V 70 211 72 factorData = true := by quickRfl

theorem kC : conjK TE.V 70 211 72 conjData = true := by quickRfl

theorem size_nGens : nGens.size = 72 := by simp [nGens]

theorem len_progY : lenLL progY = 139 := rfl

theorem hG : RepAll TE.V nGens 72 := repAll_nGens kG

theorem hV : RepAll TE.V nVals 211 := by
  have h := repAll_run (V := TE.V) (prog := progY) (by rw [size_nGens]; exact hG)
    (by rw [size_nGens]; exact TE.lines)
  rwa [size_nGens, len_progY] at h

theorem hT : Rep (nthV TE.V 70) (toMat nT) := by
  have h := hG 70 (by norm_num)
  rwa [nGens_getD (by norm_num)] at h

theorem factor : factorCheck = true := by
  unfold factorCheck
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨hg, ho, he⟩ := factor_of_factorK hV hG hT kF p hp
  rw [nGens_getD hg] at he
  rw [Bool.and_eq_true]
  exact ⟨ho, he⟩

theorem conj : conjCheck = true := by
  unfold conjCheck
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨ho, he⟩ := conj_of_conjK hV hG hT kC p hp
  rw [Bool.and_eq_true]
  exact ⟨ho, he⟩

open Certificates in
open CFSG in
theorem cert15066 : CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two.factorCheck = true ∧
    CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two.conjCheck = true := ⟨factor, conj⟩

end CertificateChecks.KernelLC.TwistedE6Two

end
