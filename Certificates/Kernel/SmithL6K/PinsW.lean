module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Kernel.SmithL6K.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem pin_wt0 : pinMapR wtC wData.toList wtd 0 349 = true := by decide +kernel

theorem pin_wt1 : pinMapR wtC wData.toList wtd 349 349 = true := by decide +kernel

theorem pin_wt2 : pinMapR wtC wData.toList wtd 698 349 = true := by decide +kernel

theorem pin_wt3 : pinMapR wtC wData.toList wtd 1047 349 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
