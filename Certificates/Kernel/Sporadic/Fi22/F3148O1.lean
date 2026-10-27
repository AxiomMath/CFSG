
module

public import Certificates.Kernel.Sporadic.Fi22.F3148D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_setreplay CertificateChecks.KernelSpor.Fi22F3148O1 3510 12 CFSG.Monster.B.Fischer.fi22OrigArrs
  CertificateChecks.KernelSpor.Fi22F3148.st1 3511 2 4 64

namespace CertificateChecks.KernelSpor.Fi22F3148

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem perm1 : allN 2 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (Fi22F3148O1.G k)
    (Fi22F3148O1.GI k)) = true := by quickRfl

theorem gens1 : allN 2 (fun k => Nat.beq (Fi22F3148O1.G k) (Fi22PC.S k)) = true := by quickRfl

theorem start1 : startK 12 182 (rowGet Fi22F3148O1.XT 2212 0) (fixL (Fi22LabX.O6 1)) = true := by
  quickRfl

theorem cnt1 : bAnd(Nat.beq (Fi22F3148O1.C 0) 1, Nat.beq (Fi22F3148O1.C 1792) 3511) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22F3148

end
