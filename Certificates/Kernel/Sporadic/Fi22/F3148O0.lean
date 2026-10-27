
module

public import Certificates.Kernel.Sporadic.Fi22.F3148D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_setreplay CertificateChecks.KernelSpor.Fi22F3148O0 3510 12 CFSG.Monster.B.Fischer.fi22OrigArrs
  CertificateChecks.KernelSpor.Fi22F3148.st0 3511 8 8 64

namespace CertificateChecks.KernelSpor.Fi22F3148

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem perm0 : allN 2 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (Fi22F3148O0.G k)
    (Fi22F3148O0.GI k)) = true := by quickRfl

theorem gens0 : allN 2 (fun k => Nat.beq (Fi22F3148O0.G k) (Fi22PC.S k)) = true := by quickRfl

theorem start0 : startK 12 54 (rowGet Fi22F3148O0.XT 676 0) (fixL (Fi22LabX.O6 0)) = true := by
  quickRfl

theorem cnt0 : bAnd(Nat.beq (Fi22F3148O0.C 0) 1, Nat.beq (Fi22F3148O0.C 448) 3511) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22F3148

end
