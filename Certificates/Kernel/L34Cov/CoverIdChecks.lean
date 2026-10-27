module

public import Certificates.Kernel.L34Cov.LiftChecks

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.ComponentClassification.GrSLit.L34Facts

theorem ch22201w_sq :
    sqData.all (fun d => cvId (wpow (tw d.1) 2) (2 * d.2.1) (2 * d.2.2.1) d.2.2.2) = true := by
  decide +kernel

theorem ch22201w_comm : commData.all (fun d =>
    cvId (commWord (tw d.1) (tw d.2.1)) d.2.2.1 d.2.2.2.1 d.2.2.2.2) = true := by
  decide +kernel

theorem ch22201w_four :
    fourthData.all (fun d => cvId (wpow (twl d.1) 4) d.2.1 d.2.2.1 d.2.2.2) = true := by
  decide +kernel

theorem ch22201w_wit : cvId (wpow witnessF 2) 0 0 0 = true ∧ cvId (wpow witnessG 2) 0 0 2 = true ∧
    cvId (wpow witnessU 2) 0 0 0 = true := by
  decide +kernel

theorem ch22201l_U : liftsK uAU uBU [(zOne, zOne, 0), (zTwo, zTwo, 0),
    (FreeGroup.invRev (tw 35), tw 35, 9), (FreeGroup.invRev (tw 38), tw 38, 39),
    (FreeGroup.invRev witnessU, witnessU, 0)] = true := by
  decide +kernel

theorem ch22201l_F : liftsK uAF uBF [(FreeGroup.invRev witnessF, witnessF, 0)] = true := by
  decide +kernel

theorem ch22201l_G : liftsK uAG uBG [(FreeGroup.invRev witnessG, witnessG, 1)] = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
