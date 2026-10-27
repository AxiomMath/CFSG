module

public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.SchreierFam.All3
public import Certificates.Data.Kernel.SchreierFam.CqK
public import Certificates.Data.Kernel.Misc.ArrEnum
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSchreierFam.J2Cq.T 9 CFSG.ComponentClassification.J2Cover.twoAArr

public section

namespace CertificateChecks.KernelSchreierFam.J2Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KS.SchreierFam
  CertificateChecks.KernelJ2Cover CFSG.ComponentClassification.J2Cover

@[expose] def cqWords : List (List Nat) := [[0], [0, 0]]

theorem tBind : arrBind twoAArr 315 9 T = true := by quickRfl

theorem tCanon : canonK 315 9 (mask 9) (315 * 9) T = true := by quickRfl

theorem cqAll : all3K 315 9 (mask 9) (315 * 9) C2A.LR C2A.TR (cqK 315 9 T C2A.S cqWords) = true := by
  quickRfl

theorem cqNeg1 : all3K 315 9 (mask 9) (315 * 9) C2A.LR C2A.TR (cqK 315 9 T C2A.S [[0]]) = false := by
  decide +kernel

theorem cqNeg0 : all3K 315 9 (mask 9) (315 * 9) C2A.LR C2A.TR (cqK 315 9 T C2A.S []) = false := by
  decide +kernel

end CertificateChecks.KernelSchreierFam.J2Cq
