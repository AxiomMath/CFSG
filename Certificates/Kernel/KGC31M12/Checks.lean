module

public import Certificates.Kernel.KGC31M12.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P

theorem kOrd : (pord 12 4 5 X5 && pord 12 4 11 X11) = true := by quickRfl

theorem kTR : TL.all (fun L => L.all fun t => permOK 12 4 (mask 4) (12 * 4) t (pinv 12 4 t)) =
    true := by quickRfl

theorem kAct5 : actAll 5 X5 = true := by quickRfl

theorem kAct11 : actAll 11 X11 = true := by quickRfl

end CertificateChecks.KernelKGC31M12

end
