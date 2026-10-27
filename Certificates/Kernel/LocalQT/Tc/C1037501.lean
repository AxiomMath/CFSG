module

public import Certificates.Data.Kernel.LocalQT.U62Gs03
public import Certificates.Kernel.LocalQT.Tc.C1037501Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KD.LQT.C1037501

open CFSG.KC.LQT.U62G

theorem hBase : baseU G Phi X Y = true := by quickRfl

theorem hC0 : classU G Phi R0 [35, 46] 63 W0 P0 X Y = true := by quickRfl

theorem hC1 : classU G Phi R1 [] 31 W1 P1 X Y = true := by quickRfl

end CertificateChecks.KD.LQT.C1037501

end
