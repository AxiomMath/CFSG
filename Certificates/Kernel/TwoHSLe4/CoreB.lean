module

public import Certificates.Kernel.TwoHSLe4.SO5D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.SO5

theorem k_nodup : CL.Nodup := by decide +kernel

theorem k_tau : CL.all (fun x => mulK x (SG 0) == mulK (SG 0) x) = true := by quickRfl

theorem k_s0 : S0L.all (fun c => CL.contains c) = true := by quickRfl

theorem k_cent : CL.all (fun x => !(S0L.all fun c => mulK c x == mulK x c ||
    mulK c x == mulK (mulK x (SG 0)) c) || D0L.contains x) = true := by
  quickRfl

theorem k_rs : CL.all (fun x => !(mulK x (SG 6) == mulK (SG 6) x) || !(mulK x (SG 7) == mulK (SG 7) x) ||
    S0L.contains x || S0L.contains (mulK (SG 0) x)) = true := by
  quickRfl

end CertificateChecks.KernelTwoHSLe4.SO5

end
