
module

public import Certificates.Kernel.Misc.Tits.Cls7050D

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Tits7050

open CertificateChecks.KernelEvenBN

theorem s11 : chkL W ((CNtC.drop 1408).take 128) 1408 = true := by decide +kernel

end CertificateChecks.KernelMisc.Tits7050

end
