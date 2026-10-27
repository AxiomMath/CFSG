module

public import Certificates.Kernel.SporSch.PairHe.GenTreesJson

public section

namespace CertificateChecks.KernelSporSch.PHeSIn

meta def js : String := include_str "S2Data.json"

end CertificateChecks.KernelSporSch.PHeSIn

#kss_treesjson CertificateChecks.KernelSporSch.PHeS CertificateChecks.KernelSporSch.PHeSIn.js

end
