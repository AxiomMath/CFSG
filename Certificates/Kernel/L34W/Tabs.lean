module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.GrSLitL34FactsRealReps
meta import Certificates.Data.GrSLitL34FactsRealReps

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelL34W.T1X CFSG.ComponentClassification.GrSLit.L34Facts.Real.realT1Hex
#kmisc_hexflat CertificateChecks.KernelL34W.T1X
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.realT1Hex 3 64 12 64

#ks_chars CertificateChecks.KernelL34W.AlX
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.realAlphaHex
#kmisc_hexflat CertificateChecks.KernelL34W.AlX
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.realAlphaHex 3 66 12 36

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KC.L34W

theorem bounds_k : boundsOK T1X.F AlX.F = true := by decide +kernel

theorem bounds_neg : (!boundsOK (patchT T1X.F 0 (Nat.lor (T1X.F 0) 4095)) AlX.F) = true := by
  decide +kernel

end CertificateChecks.KernelL34W

end
