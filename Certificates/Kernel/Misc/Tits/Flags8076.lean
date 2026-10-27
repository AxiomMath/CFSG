module

public import Certificates.Kernel.SporSch.Tits.GenList
public import CFSG.Quasithin.Recognition.CertTitsOvergroupCheckInputs
public meta import CFSG.Quasithin.Recognition.CertTitsOvergroupCheckInputs

public section

namespace CertificateChecks.KernelMisc.Tits8076

meta def dFlags : List (Array Nat) := CFSG.Sporadic.Schreier.Tits.titsTFlagArrs.toList
meta def sFlags : List (Array Nat) := CFSG.Quasithin.titsSFlagArrs.toList

end CertificateChecks.KernelMisc.Tits8076

#kst_plist CertificateChecks.KernelMisc.Tits8076.TitsFL 14 CertificateChecks.KernelMisc.Tits8076.dFlags
#kst_plist CertificateChecks.KernelMisc.Tits8076.TitsSL 14 CertificateChecks.KernelMisc.Tits8076.sFlags

end
