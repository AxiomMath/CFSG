module

public import Certificates.Kernel.SporSch.PairJ3.C81Fns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem five_sq : bIf(eqOnL bs (powF (fun x => powF (nfp 281475052077923) 1
    (nfp 281474999390686 (powF (nfp 281475052077923) 1 (nfi 281474999390686 x)))) 2)
    (fun x => x), false, true) = true := by
  quickRfl

theorem neg_five_six : bIf(eqOnL bs (powF (fun x => powF (nfp 281475052077923) 1
    (nfp 281474999390686 (powF (nfp 281475052077923) 1 (nfi 281474999390686 x)))) 6)
    (fun x => x), false, true) = false := by
  decide +kernel

end CertificateChecks.KernelSporSch.PJ3C81

end
