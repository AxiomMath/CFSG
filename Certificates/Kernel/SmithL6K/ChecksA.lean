module

public import Certificates.Data.Kernel.SmithL6KA
public import Certificates.Kernel.SmithL6K.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem wtd_ne0 : wtd.all (· != 0) = true := by decide +kernel

theorem adj_row0 : (List.range 1395).any (fun j =>
    atLeast4 (wmk.getD 0 0 &&& wmk.getD j 0) && wtd.getD j 0 != wtd.getD 0 0) = true := by
  decide +kernel

theorem sum_row0 : sumRowK (maskOf wtd) (wtd.getD 0 0) (wmk.getD 0 0) wtd wmk = true := by
  decide +kernel

end CertificateChecks.KernelSmithL6K
