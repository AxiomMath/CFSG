
module

public import Certificates.Kernel.LocalComp.Census.Data
public import CFSG.Certificates.Kernel.CensusFormSound
public import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Fischer.F4
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusCertBase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.CensusM

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.KC.CensusForm CFSG.ComponentClassification.AS81.Census
  CertificateChecks.KernelLC.CensusD CFSG.PSL3Four.Native

@[expose] noncomputable def unpackM (P : Nat) : Array Nat :=
  Array.ofFn (n := 6) fun k => fld(P, Nat.mul (nat_lit 12) k.val, nat_lit 4095)

@[expose] def badMatK (x : Nat × Nat × List Nat) : Array Nat :=
  wordMat #[g1M, g2M, if x.2.1 = 0 then (rootsM[x.1]!).1 else matMul (rootsM[x.1]!).1 tauM,
    if x.2.1 = 0 then (rootsM[x.1]!).2 else matMul tauM (rootsM[x.1]!).2] x.2.2

@[expose] noncomputable def tabC (i : Nat) : Bool := tabK (unpackM (IM i)) (MB i) (ML i) (MH i)

@[expose] noncomputable def isoC (i : Nat) : Bool := isomK (QT 0) (ML i) (MH i)

end CertificateChecks.KernelLC.CensusM

#kss_each CertificateChecks.KernelLC.CensusT CertificateChecks.KernelLC.CensusM.tabC 87
#kss_each CertificateChecks.KernelLC.CensusI CertificateChecks.KernelLC.CensusM.isoC 87

namespace CertificateChecks.KernelLC.CensusM

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.KC.CensusForm CFSG.ComponentClassification.AS81.Census
  CertificateChecks.KernelLC.CensusD CFSG.PSL3Four.Native

theorem qt_ok : qtK (QT 0) = true := by quickRfl

theorem pre_unpackM (P : Nat) :
    ((unpackM P).size == 6 && allBelow 6 fun i => decide ((unpackM P)[i]! < 4096)) = true := by
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.ComponentClassification.PSL3Four.allBelow_eq_true,
    decide_eq_true_eq]
  refine ⟨by simp [unpackM], fun i hi => ?_⟩
  rw [unpackM, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
  exact fld_lt _ _ 12

theorem isom_IM {i : Nat} (hi : i < 87) : isomOK (unpackM (IM i)) = true :=
  isomOK_of_isomK (pre_unpackM _) (CensusT.all i hi) qt_ok (CensusI.all i hi)

theorem img_IM {i : Nat} (hi : i < 87) {v : Nat} (hv : v < 4096) :
    img (ML i) (MH i) v = applyC (unpackM (IM i)) v :=
  img_eq (CensusT.all i hi) hv

theorem b_x0 : x0M = unpackM (IM 0) := by decide +kernel
theorem b_tau : tauM = unpackM (IM 1) := by decide +kernel
theorem b_c : cM = unpackM (IM 2) := by decide +kernel
theorem b_b3 : b3M = unpackM (IM 3) := by decide +kernel
theorem b_b5 : b5M = unpackM (IM 4) := by decide +kernel
theorem b_g1 : g1M = unpackM (IM 5) := by decide +kernel
theorem b_g2 : g2M = unpackM (IM 6) := by decide +kernel
theorem b_g1i : g1iM = unpackM (IM 7) := by decide +kernel
theorem b_g2i : g2iM = unpackM (IM 8) := by decide +kernel

theorem b_root : ∀ j < 20, (rootsM[j]!).1 = unpackM (IM (9 + 2 * j)) ∧
    (rootsM[j]!).2 = unpackM (IM (10 + 2 * j)) := by decide +kernel

theorem b_good : ∀ e < 3, (goodData[e]!).2.1 = unpackM (IM (49 + 2 * e)) ∧
    (goodData[e]!).2.2 = unpackM (IM (50 + 2 * e)) := by decide +kernel

theorem b_bad : ∀ e < 32, badMatK badData[e]! = unpackM (IM (55 + e)) := by decide +kernel

end CertificateChecks.KernelLC.CensusM

end
