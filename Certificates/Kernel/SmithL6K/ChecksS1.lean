module

public import Certificates.Data.Kernel.SmithL6KS
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.RangeGlue
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem sRows1_q : ∀ q < 4, sRowsK tvc tcl (maskOf wtd) (1 + q * 122) 122 = true := by
  kc_cover 1

theorem sRows1_ok : sRowsK tvc tcl (maskOf wtd) 1 488 = true :=
  sRowsK_of_chunks tvc tcl (maskOf wtd) 1 4 122 488 rfl sRows1_q

end CertificateChecks.KernelSmithL6K
