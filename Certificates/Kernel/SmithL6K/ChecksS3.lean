module

public import Certificates.Data.Kernel.SmithL6KS
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.RangeGlue
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem sRows3_q : ∀ q < 4, sRowsK tvc tcl (maskOf wtd) (977 + q * 122) 122 = true := by
  kc_cover 1

theorem sRows3_ok : sRowsK tvc tcl (maskOf wtd) 977 488 = true :=
  sRowsK_of_chunks tvc tcl (maskOf wtd) 977 4 122 488 rfl sRows3_q

end CertificateChecks.KernelSmithL6K
