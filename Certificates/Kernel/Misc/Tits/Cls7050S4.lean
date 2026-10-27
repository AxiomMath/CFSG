
module

public import Certificates.Kernel.Misc.Tits.Cls7050D

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Tits7050

open CertificateChecks.KernelEvenBN

theorem s4 : chkL W ((CNtC.drop 512).take 128) 512 = true := by decide +kernel

end CertificateChecks.KernelMisc.Tits7050

end
