module

public import Certificates.Kernel.HS100.S5OCData
public import Certificates.Kernel.HS100.S5OData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

theorem OC.gensX : (allN 7 fun k => Nat.beq (OC.G k) (OX.F (k + 7))) = true := by quickRfl

theorem OC.card : Nat.beq OC.N 40320 = true := by quickRfl

theorem OC.keys : keysSK 100 7 [0, 1, 2, 3, 4] OC.N OC.T OC.SK = true := by quickRfl

end CertificateChecks.KernelHS100

end
