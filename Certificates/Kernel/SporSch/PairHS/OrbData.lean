module

public import Certificates.Kernel.SporSch.PairHe.GenTreesJson

public section

namespace CertificateChecks.KernelSporSch.PHSOIn

meta def js : String := include_str "data/Orb.json"

end CertificateChecks.KernelSporSch.PHSOIn

#kss_treesjson CertificateChecks.KernelSporSch.PHSO CertificateChecks.KernelSporSch.PHSOIn.js

end
