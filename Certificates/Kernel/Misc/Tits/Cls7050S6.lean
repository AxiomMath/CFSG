
module

public import Certificates.Kernel.Misc.Tits.Cls7050D

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Tits7050

open CertificateChecks.KernelEvenBN

theorem s6 : chkL W ((CNtC.drop 768).take 128) 768 = true := by decide +kernel

end CertificateChecks.KernelMisc.Tits7050

end
