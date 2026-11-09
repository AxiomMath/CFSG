module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.UnitarySix.Sec3.Arrs
meta import Certificates.Kernel.UnitarySix.Sec3.Arrs
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Fischer.T46Unitary
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.Fischer.T46Unitary
meta import CFSG.LieType.BorelTits.CompleteFlag
meta import CFSG.LieType.Chevalley.C2E6StandardFixedData
meta import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelU6.Sec3.CK1A1 693 10 64 64
  CertificateChecks.KernelU6.Sec3.sK1A1 CertificateChecks.KernelU6.Sec3.bK1A1 14
  CertificateChecks.KernelU6.Sec3.dK1A1

#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1A1 0 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1A1 1 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1A1 2 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1A1 3 0 11

#ks_rawchain_sl2_sch CertificateChecks.KernelU6.Sec3.CK1A1 1 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelU6.Sec3.CK1A1 2 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelU6.Sec3.CK1A1 3 0 1

namespace CertificateChecks.KernelU6.Sec3

@[expose] def wK1A1 : List (List Nat) :=
  [[2, 1, 2, 0, 2, 1, 2, 0], [0], [2, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1], [1], [2], [3],
    [1, 3, 0, 3, 0, 1], [1, 3, 1], [3, 0, 3, 0], [2, 1, 3, 1, 2], [3, 2, 0, 3, 0, 2],
    [1, 2, 1, 3, 1, 2, 1], [1, 3, 2, 0, 3, 0, 2, 1],
    [3, 0, 2, 1, 3, 1, 2, 0, 3, 0, 2, 1, 3, 1, 2, 0]]

end CertificateChecks.KernelU6.Sec3

#ks_rawchain_sl2_osub CertificateChecks.KernelU6.Sec3.CK1A1 1 3 4 5
  CertificateChecks.KernelU6.Sec3.wK1A1
#ks_rawchain_sl2_scho CertificateChecks.KernelU6.Sec3.CK1A1 0 8

#ks_rawchain_sl2_joino CertificateChecks.KernelU6.Sec3.CK1A1

end
