module

public import Certificates.Data.Kernel.SmithEKC
public import Certificates.Kernel.SmithEK.Cols
public import Certificates.Kernel.UnitarySix.Tables

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21260conj : chkCF cs.L CertificateChecks.KernelU6.T.R = true := by
  decide +kernel

theorem c21260neg_cols : chkCF (cs.L.set 0 (cs.L.getD 1 [])) CertificateChecks.KernelU6.T.R =
    false := by
  decide +kernel

theorem c21260neg_row : chkCF cs.L (fun j => if j = 0 then CertificateChecks.KernelU6.T.R 1
    else CertificateChecks.KernelU6.T.R j) = false := by
  decide +kernel

theorem c21260neg_high : chkCF cs.L (fun j => if j = 0 then
    CertificateChecks.KernelU6.T.R 0 + 2 ^ 6930 else CertificateChecks.KernelU6.T.R j) = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
