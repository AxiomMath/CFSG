module

public import Certificates.Kernel.KGC31M12.Defs
public import Certificates.Kernel.KGC31M12.Act
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P

theorem kOrd : (pord 12 4 5 X5 && pord 12 4 11 X11) = true := by quickRfl

theorem kTR : TL.all (fun L => L.all fun t => permOK 12 4 (mask 4) (12 * 4) t (pinv 12 4 t)) =
    true := by quickRfl

theorem kAct5 : actAll 5 X5 = true := actAll_of_R fun _ h => by
  unfold actR at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem kAct11 : actAll 11 X11 = true := actAll_of_R fun _ h => by
  unfold actR at h
  rw [Bool.and_eq_true] at h
  exact h.2

end CertificateChecks.KernelKGC31M12

end
