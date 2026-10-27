module

public import Certificates.Data.Kernel.SmithL6KS
public import Certificates.Kernel.SmithL6K.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem sTcl_length : tcl.length = 1953 := by decide +kernel

theorem sPair00_ok : sPairK (tvc.getD 0 0) (tcl.getD 0 []) (tvc.getD 0 0, tcl.getD 0 []) = true := by
  decide +kernel

theorem sSpan0_ok : CFSG.SmithE.K.spanOKL (tcl.getD 0 []) = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
