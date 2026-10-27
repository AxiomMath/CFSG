module

public import Certificates.Kernel.SporSch.PairBT.McLData
public import Certificates.Kernel.SporSch.PairBT.GenSyl
public meta import Certificates.Kernel.SporSch.PairBT.McLData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLBT

meta def sylHint : String := include_str "McLSyl.txt"

end CertificateChecks.KernelSporSch.McLBT

#kss_reps CertificateChecks.KernelSporSch.McLSyl 275 9 CertificateChecks.KernelSporSch.McLBT.sylHint

end
