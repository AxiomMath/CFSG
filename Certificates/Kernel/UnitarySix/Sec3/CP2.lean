module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.UnitarySix.Sec3.Arrs2
meta import Certificates.Kernel.UnitarySix.Sec3.Arrs2
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Fischer.T46Unitary
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.Fischer.T46Unitary
meta import CFSG.LieType.BorelTits.CompleteFlag
meta import CFSG.LieType.Chevalley.C2E6StandardFixedData
meta import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelU6.Sec3.CP2 693 10 64 64
  CertificateChecks.KernelU6.Sec3.sP2 CertificateChecks.KernelU6.Sec3.bP2 17
  CertificateChecks.KernelU6.Sec3.dP2

#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CP2 0 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CP2 1 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CP2 2 0 11

#ks_rawchain_sl2_sch CertificateChecks.KernelU6.Sec3.CP2 1 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelU6.Sec3.CP2 2 0 2

namespace CertificateChecks.KernelU6.Sec3

@[expose] def wSubP2 : List (List Nat) :=
  [[0], [1], [2], [3], [4], [5], [2, 5, 1, 5, 1, 2], [2, 5, 2], [5, 1, 5, 1], [4, 5, 4],
    [4, 2, 5, 1, 5, 4, 1, 2], [4, 2, 5, 4, 2], [4, 5, 1, 5, 4, 1], [5, 3, 5, 4, 5, 4, 3],
    [5, 3, 0, 5, 3, 0, 5, 3, 0, 5, 3, 0], [5, 3, 1, 5, 3, 1, 5, 3, 1, 5, 3, 1],
    [2, 5, 3, 5, 4, 5, 4, 3, 2]]

end CertificateChecks.KernelU6.Sec3

#ks_rawchain_sl2_osub CertificateChecks.KernelU6.Sec3.CP2 0 1 2 3 4 5
  CertificateChecks.KernelU6.Sec3.wSubP2
#ks_rawchain_sl2_scho CertificateChecks.KernelU6.Sec3.CP2 0 10

#ks_rawchain_sl2_joino CertificateChecks.KernelU6.Sec3.CP2

end
