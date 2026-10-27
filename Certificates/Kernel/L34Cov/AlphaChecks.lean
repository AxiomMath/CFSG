module

public import Certificates.Data.Kernel.L34Cov.Alpha
public import Certificates.Kernel.L34Cov.Words
public import Certificates.Kernel.L34Cov.Checks
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration

#kc_each CertificateChecks.KernelL34Cov.ch22219al a
  (fun i => alphaOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW (UAC.codes.getD i [])
    (UBC.codes.getD i [])) 0 36

theorem ch22219al_neg1 : (!alphaOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW
    ((UAC.codes.getD 1 []).drop 1) (UBC.codes.getD 1 [])) = true := by
  decide +kernel

theorem ch22219al_neg2 : (!alphaOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW [0] [2, 2]) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
