module

public import Certificates.Kernel.MinusQuandle.Data
public import Certificates.Data.Kernel.MinusSecondKind

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMinusSK

open CFSG.KD.MinusSecondKind CertificateChecks.KernelMinusQ

theorem inv_ok : invOK R = true := by decide +kernel

theorem quandle_ok : quandleOK R = true := by decide +kernel

theorem base_ok : baseOK R = true := by decide +kernel

theorem sk_ok : skOK R = true := by decide +kernel

end CertificateChecks.KernelMinusSK
