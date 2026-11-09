module

public import Certificates.Kernel.SporSch.PairHe.GenTreesJson

public section

namespace CertificateChecks.KernelSporSch.PHeOIn

meta def js : String := include_str "data/Orb.json"

end CertificateChecks.KernelSporSch.PHeOIn

#kss_treesjson CertificateChecks.KernelSporSch.PHeO CertificateChecks.KernelSporSch.PHeOIn.js

end
