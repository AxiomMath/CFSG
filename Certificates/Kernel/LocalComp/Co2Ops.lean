module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.CFSGNative.Co2.Data
meta import Certificates.Data.CFSGNative.Co2.Data
public import Certificates.Data.CFSGNative.Filter.Co2Data
public import Certificates.Data.RankThree46F2.Co2
public import Certificates.Data.KFCub2Co2
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Kernel.LocalComp.M1Gen
public import CFSG.Certificates.Kernel.LocalCompCubSound

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.Co2Ops.SA CFSG.Sporadic.Co2.Native.seedA
#lc_m1 CertificateChecks.KernelLC.Co2Ops.SA CFSG.Sporadic.Co2.Native.seedA 22
#ks_chars CertificateChecks.KernelLC.Co2Ops.SB CFSG.Sporadic.Co2.Native.seedB
#lc_m1 CertificateChecks.KernelLC.Co2Ops.SB CFSG.Sporadic.Co2.Native.seedB 22

namespace CertificateChecks.KernelLC.Co2Ops

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census

theorem sec_K : secK 22 SA.M SB.M co2Sec = true := by decide +kernel

theorem w4_K : w4K 22 SA.M SB.M co2W3.base co2W3.inv = true := by decide +kernel

theorem cub2_K : cub2K 22 SA.M SB.M co2FiveData = true := by decide +kernel

theorem cub_K : CFSG.KC.LocalComp.Cub.cubicK 22 SA.M SB.M co2MultData = true := by
  decide +kernel

theorem sec_neg : (!secK 22 SA.M SB.M { co2Sec with outs := [25, 25, 29, 31, 33] }) = true := by
  decide +kernel

theorem w4_neg : (!w4K 22 SA.M SB.M co2W3.base 0) = true := by decide +kernel

theorem cub2_neg : (!cub2K 22 SA.M SB.M { co2FiveData with r := co2FiveData.r + 1 }) = true := by
  decide +kernel

theorem sec_neg_seeds : (!secK 22 SB.M SA.M co2Sec) = true := by decide +kernel

end CertificateChecks.KernelLC.Co2Ops

end
