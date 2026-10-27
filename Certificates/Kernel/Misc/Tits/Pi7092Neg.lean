module

public import Certificates.Kernel.Misc.Tits.Pi7092

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.TitsPi

open CFSG.KC.TitsPi CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor.Tits2264

theorem neg_sift : siftD P = false := by decide +kernel

end CertificateChecks.KernelMisc.TitsPi

end
