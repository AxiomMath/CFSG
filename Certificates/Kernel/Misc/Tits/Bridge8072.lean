module

public import Certificates.Data.Kernel.Misc.TitsBridge
public import Certificates.Kernel.Misc.Tits.Text
public import CFSG.Open.QuasithinDefs

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.TitsB1 CFSG.Open.quasithinTitsData1
#ks_chars CertificateChecks.KernelMisc.TitsB2 CFSG.Open.quasithinTitsData2

public section

namespace CertificateChecks.KernelMisc.TitsB

open CFSG.KC.TitsBridge

theorem bridge₁ : bridgeK (TitsText.F 18) TitsB1.chars = true := by decide +kernel

theorem bridge₂ : bridgeK (TitsText.F 19) TitsB2.chars = true := by decide +kernel

end CertificateChecks.KernelMisc.TitsB

end
