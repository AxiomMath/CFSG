module

public import Certificates.Data.Kernel.SmithL6KF
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataF

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem fWord_ok : fWordK tvc tcl wtd fs0 fe = true := by decide +kernel

theorem fPlane_ok : fPlaneK tvc tcl fe fp = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
