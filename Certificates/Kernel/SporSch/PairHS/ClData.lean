module

public import Certificates.Kernel.SporSch.PairHS.Chain
public import Certificates.Kernel.SporSch.PairHS.GenClTJson

public section

namespace CertificateChecks.KernelSporSch.PHSJIn

meta def js : String := include_str "ClData.json"

end CertificateChecks.KernelSporSch.PHSJIn

#kss_cltjson CertificateChecks.KernelSporSch.PHST CertificateChecks.KernelSporSch.PHSJIn.js "A"

#kss_cltjson CertificateChecks.KernelSporSch.PHSU CertificateChecks.KernelSporSch.PHSJIn.js "B"

#kss_cltjson CertificateChecks.KernelSporSch.PHSJ CertificateChecks.KernelSporSch.PHSJIn.js "J"

end
