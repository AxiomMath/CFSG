module

public import Certificates.Data.Kernel.SmithL6KQ
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataO
public import Certificates.Kernel.SmithL6K.DataQ

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem qa_ok : qaChkK wtd wmk tcl p0 qg qu = true := by decide +kernel

theorem cv_ok : cvChkK wtd tcl p0 cg cu = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
