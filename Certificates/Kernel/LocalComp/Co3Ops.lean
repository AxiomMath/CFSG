module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.CFSGNative.Co3.Data
meta import Certificates.Data.CFSGNative.Co3.Data
public import Certificates.Data.CFSGNative.Filter.Co3Data
public import Certificates.Data.KFCub2Co3
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Kernel.LocalComp.M1Gen
public import CFSG.Certificates.Kernel.LocalCompCubSound

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.Co3Ops.SA CFSG.Sporadic.Co3.Native.seedA
#lc_m1 CertificateChecks.KernelLC.Co3Ops.SA CFSG.Sporadic.Co3.Native.seedA 22
#ks_chars CertificateChecks.KernelLC.Co3Ops.SB CFSG.Sporadic.Co3.Native.seedB
#lc_m1 CertificateChecks.KernelLC.Co3Ops.SB CFSG.Sporadic.Co3.Native.seedB 22

namespace CertificateChecks.KernelLC.Co3Ops

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem sec_K : secK 22 SA.M SB.M co3Sec = true := by decide +kernel

theorem cub2_K : cub2K 22 SA.M SB.M co3FiveData = true := by decide +kernel

theorem cub_K : CFSG.KC.LocalComp.Cub.cubicK 22 SA.M SB.M co3MultData = true := by
  decide +kernel

theorem sec_neg : (!secK 22 SA.M SB.M { co3Sec with outs := [37, 37, 43, 47, 50] }) = true := by
  decide +kernel

theorem cub2_neg : (!cub2K 22 SA.M SB.M { co3FiveData with r := co3FiveData.r + 1 }) = true := by
  decide +kernel

theorem cub_neg : (!CFSG.KC.LocalComp.Cub.cubicK 22 SB.M SA.M co3MultData) = true := by
  decide +kernel

end CertificateChecks.KernelLC.Co3Ops

end
