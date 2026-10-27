module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.CFSGNative.Ru.Data
meta import Certificates.Data.CFSGNative.Ru.Data
public import Certificates.Data.CFSGNative.Filter.RuData
public import Certificates.Kernel.LocalComp.M1Gen

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.RuOps.SA CFSG.Sporadic.Ru.Native.seedA
#lc_m1 CertificateChecks.KernelLC.RuOps.SA CFSG.Sporadic.Ru.Native.seedA 28
#ks_chars CertificateChecks.KernelLC.RuOps.SB CFSG.Sporadic.Ru.Native.seedB
#lc_m1 CertificateChecks.KernelLC.RuOps.SB CFSG.Sporadic.Ru.Native.seedB 28

namespace CertificateChecks.KernelLC.RuOps

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem sec_K : secK 28 SA.M SB.M ruSec = true := by decide +kernel

theorem sec_neg : (!secK 28 SA.M SB.M { ruSec with outs := [14, 14, 18, 20, 22] }) = true := by
  decide +kernel

end CertificateChecks.KernelLC.RuOps

end
