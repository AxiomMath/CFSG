module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Kernel.SmithL6K.Data

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem pin_cols0 : pinMapR colsL tvList.toList tcl 0 489 = true := by decide +kernel

theorem pin_cols1 : pinMapR colsL tvList.toList tcl 489 489 = true := by decide +kernel

theorem pin_cols2 : pinMapR colsL tvList.toList tcl 978 489 = true := by decide +kernel

theorem pin_cols3 : pinMapR colsL tvList.toList tcl 1467 489 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
