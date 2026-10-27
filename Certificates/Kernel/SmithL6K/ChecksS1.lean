module

public import Certificates.Data.Kernel.SmithL6KS
public import Certificates.Kernel.SmithL6K.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem sRows1_ok : sRowsK tvc tcl (maskOf wtd) 1 488 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
