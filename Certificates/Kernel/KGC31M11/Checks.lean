module

public import Certificates.Kernel.KGC31M11.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M11

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P

theorem kOrd : (pord 11 4 5 X5 && pord 11 4 11 X11) = true := by quickRfl

theorem kTR : TL.all (fun L => L.all fun t => permOK 11 4 (mask 4) (11 * 4) t (pinv 11 4 t)) =
    true := by quickRfl

theorem kAct5 : actAll 5 X5 = true := by quickRfl

theorem kAct11 : actAll 11 X11 = true := by quickRfl

end CertificateChecks.KernelKGC31M11

end
