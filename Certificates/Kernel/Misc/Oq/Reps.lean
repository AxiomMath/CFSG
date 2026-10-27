module

public import Certificates.Data.Kernel.Misc.OqBlk

public section

namespace CertificateChecks.KernelMisc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Misc.Oq

theorem repL : repOK 0 (repP false) (brP false) (krP false) (stabP false) (invD false)
    (certD false) 49 1152 72 = true := by decide +kernel

theorem repU : repOK 1 (repP true) (brP true) (krP true) (stabP true) (invD true)
    (certD true) 63 5760 120 = true := by decide +kernel

end CertificateChecks.KernelMisc.Oq

end
