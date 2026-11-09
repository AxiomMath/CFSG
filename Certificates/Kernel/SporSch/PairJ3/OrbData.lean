module

public import Certificates.Kernel.SporSch.PairHe.GenTreesJson

public section

namespace CertificateChecks.KernelSporSch.PJ3OIn

meta def js : String := include_str "data/Orb.json"

end CertificateChecks.KernelSporSch.PJ3OIn

#kss_treesjson CertificateChecks.KernelSporSch.PJ3O CertificateChecks.KernelSporSch.PJ3OIn.js

end
