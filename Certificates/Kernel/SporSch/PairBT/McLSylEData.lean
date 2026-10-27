module

public import Certificates.Kernel.SporSch.PairBT.McLData
public import Certificates.Kernel.SporSch.PairBT.GenSyl
public import Certificates.Kernel.SporSch.PairBT.GenSylElts
public meta import Certificates.Kernel.SporSch.PairBT.McLData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLBT

meta def syl2Hint : String := include_str "McLSyl2.txt"

meta def syl5Hint : String := include_str "McLSyl5.txt"

meta def syl5RHint : String := include_str "McLSyl5R.txt"

end CertificateChecks.KernelSporSch.McLBT

#kss_reps CertificateChecks.KernelSporSch.McLSyl5R 275 9
  CertificateChecks.KernelSporSch.McLBT.syl5RHint

namespace CertificateChecks.KernelSporSch.McLBT

@[expose] noncomputable def RL2 : List Nat := [CertificateChecks.KernelSporSch.PMcL.S 0]

@[expose] noncomputable def R1 : Nat := CertificateChecks.KernelSporSch.McLSyl5R.XL.getD 0 0

@[expose] noncomputable def R2 : Nat := CertificateChecks.KernelSporSch.McLSyl5R.XL.getD 1 0

@[expose] noncomputable def RL5 : List Nat := [R1, R2]

end CertificateChecks.KernelSporSch.McLBT

end
