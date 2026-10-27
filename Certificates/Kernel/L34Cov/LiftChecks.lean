module

public import Certificates.Data.Kernel.L34Cov.Lift
public import Certificates.Kernel.L34Cov.Checks
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLiftCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4WitCertInputs

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.GrS4

@[expose] noncomputable def liftsK (uA uB : List (Fin 2 × Bool))
    (L : List (List (Fin 2 × Bool) × List (Fin 2 × Bool) × Nat)) : Bool :=
  liftsOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW (uA.map letterCode) (uB.map letterCode)
    (liftCodes L)

theorem ch22234l_k : liftsK uAF uBF [([], zOne, 12), ([], zTwo, 45)] = true := by decide +kernel

theorem ch22212l_F : liftsK uAF uBF [(FreeGroup.invRev liftW0, liftW0, 2)] = true := by
  decide +kernel

theorem ch22212l_G : liftsK uAG uBG [(FreeGroup.invRev liftW0, liftW0, 2)] = true := by
  decide +kernel

theorem ch22212l_U : liftsK uAU uBU [(FreeGroup.invRev liftW0, liftW0, 0)] = true := by
  decide +kernel

theorem ch22212l_sq : cvId (wpow liftW0 2) 0 0 1 = true := by decide +kernel

theorem ch22900l_F : liftsK uAF uBF [(FreeGroup.invRev witF, witF, 2)] = true := by
  decide +kernel

theorem ch22900l_G : liftsK uAG uBG [(FreeGroup.invRev witG, witG, 0)] = true := by
  decide +kernel

theorem ch22900l_U : liftsK uAU uBU [(FreeGroup.invRev witU, witU, 0)] = true := by
  decide +kernel

theorem ch22900l_sq : cvId (wpow witF 2) 0 0 1 = true ∧ cvId (wpow witG 2) 0 0 0 = true ∧
    cvId (wpow witU 2) 0 0 1 = true := by
  decide +kernel

theorem ch6147l_k : cvId (commWord (tw 35) (tw 18)) 2 1 0 = true ∧
    cvId (commWord (tw 38) (tw 19)) 1 3 0 = true ∧
    cvId (commWord (tw 49) (tw 23)) 3 2 0 = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
