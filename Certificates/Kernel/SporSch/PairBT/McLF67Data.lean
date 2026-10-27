module

public import Certificates.Kernel.SporSch.PairBT.McLData
public import Certificates.Kernel.SporSch.PairBT.GenSyl
public meta import Certificates.Kernel.SporSch.PairBT.McLData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLBT

meta def f67Hint : String := include_str "McLF67.txt"

end CertificateChecks.KernelSporSch.McLBT

#kss_reps CertificateChecks.KernelSporSch.McLF67R 275 9 CertificateChecks.KernelSporSch.McLBT.f67Hint

namespace CertificateChecks.KernelSporSch.McLBT

@[expose] noncomputable def Z7 : Nat := CertificateChecks.KernelSporSch.McLF67R.XL.getD 0 0

@[expose] noncomputable def X15 : Nat := CertificateChecks.KernelSporSch.McLF67R.XL.getD 1 0

end CertificateChecks.KernelSporSch.McLBT

end
