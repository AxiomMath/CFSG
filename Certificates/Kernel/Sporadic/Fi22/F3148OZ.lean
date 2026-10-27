
module

public import Certificates.Kernel.Sporadic.Fi22.F3148D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_setreplay CertificateChecks.KernelSpor.Fi22F3148OZ 3510 12 CFSG.Monster.B.Fischer.fi22OrigArrs
  CertificateChecks.KernelSpor.Fi22F3148.stZ 3510 1 2 64

namespace CertificateChecks.KernelSpor.Fi22F3148

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem permZ : allN 2 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (Fi22F3148OZ.G k)
    (Fi22F3148OZ.GI k)) = true := by quickRfl

theorem gensZ : allN 2 (fun k => Nat.beq (Fi22F3148OZ.G k) (Fi22PC.S k)) = true := by quickRfl

theorem startZ : startK 12 694 (rowGet Fi22F3148OZ.XT 8356 0) (fixL Fi22E2073.E) = true := by
  quickRfl

theorem cntZ : bAnd(Nat.beq (Fi22F3148OZ.C 0) 1, Nat.beq (Fi22F3148OZ.C 3520) 3510) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22F3148

end
