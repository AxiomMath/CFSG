module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.RangeGlue
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem pin_cols0_q : ∀ q < 3, pinMapR colsL tvList.toList tcl (0 + q * 163) 163 = true := by
  kc_cover 1

theorem pin_cols0 : pinMapR colsL tvList.toList tcl 0 489 = true :=
  pinMapR_of_chunks colsL tvList.toList tcl 0 3 163 489 rfl pin_cols0_q

theorem pin_cols1_q : ∀ q < 3, pinMapR colsL tvList.toList tcl (489 + q * 163) 163 = true := by
  kc_cover 1

theorem pin_cols1 : pinMapR colsL tvList.toList tcl 489 489 = true :=
  pinMapR_of_chunks colsL tvList.toList tcl 489 3 163 489 rfl pin_cols1_q

theorem pin_cols2_q : ∀ q < 3, pinMapR colsL tvList.toList tcl (978 + q * 163) 163 = true := by
  kc_cover 1

theorem pin_cols2 : pinMapR colsL tvList.toList tcl 978 489 = true :=
  pinMapR_of_chunks colsL tvList.toList tcl 978 3 163 489 rfl pin_cols2_q

theorem pin_cols3_q : ∀ q < 3, pinMapR colsL tvList.toList tcl (1467 + q * 163) 163 = true := by
  kc_cover 1

theorem pin_cols3 : pinMapR colsL tvList.toList tcl 1467 489 = true :=
  pinMapR_of_chunks colsL tvList.toList tcl 1467 3 163 489 rfl pin_cols3_q

end CertificateChecks.KernelSmithL6K
