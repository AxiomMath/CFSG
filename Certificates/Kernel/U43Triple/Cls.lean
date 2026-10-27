module

public import Certificates.Kernel.U43Triple.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU43T

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.InvCls

theorem clsT : CFSG.KC.LQT.P.allN 128 (clsAt 820 10 (pidn 820 10) 128 7 E R CL) = true := by
  decide +kernel

theorem repT : CFSG.KC.LQT.P.allN 7 (repAt 820 10 A 3 (A 0) 128 E R RW) = true := by
  decide +kernel

end CertificateChecks.KernelU43T

end
