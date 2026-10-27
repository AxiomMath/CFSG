module

public import Certificates.Data.Kernel.SmithL6KU
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataO

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem ua_rows5_ok : uaRowsC (ugC tvc) tvc (((uaRC tvc p0).drop 35).take 7) = true := by
  decide +kernel

end CertificateChecks.KernelSmithL6K
