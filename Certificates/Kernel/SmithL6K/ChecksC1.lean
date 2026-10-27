module

public import Certificates.Data.Kernel.SmithL6KC
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataC

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6.K

theorem cx_scan1 : scanC tvc tcP cxU cxL cxRM 1 cxS1 0 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
