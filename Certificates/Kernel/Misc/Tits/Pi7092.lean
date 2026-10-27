module

public import Certificates.Data.Kernel.Misc.TitsPi
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.Tits.Sift2264
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
meta import CFSG.Quasithin.Recognition.CertDataTitsOuter

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelMisc.TitsPi.P 11 CFSG.Quasithin.titsPiArr

public section

namespace CertificateChecks.KernelMisc.TitsPi

open CFSG.KC.TitsPi CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor.Tits2264

theorem bind : cmpL 1755 11 P 0 CFSG.Quasithin.titsPiArr.toList = true := by decide +kernel

theorem perm : permC P = true := by decide +kernel

theorem permGI : permC (GI 1) = true := by decide +kernel

theorem sift : siftD (pcomp 1755 11 (mask 11) P (GI 1)) = true ∧
    permC (pcomp 1755 11 (mask 11) P (GI 1)) = true := by decide +kernel

end CertificateChecks.KernelMisc.TitsPi

end
