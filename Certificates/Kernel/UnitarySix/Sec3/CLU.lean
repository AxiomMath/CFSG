module

public import Certificates.Kernel.UnitarySix.Sec3.CLD
public import Certificates.Kernel.Sporadic.RawGenSchPU
meta import Certificates.Kernel.UnitarySix.Sec3.Arrs
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.Fischer.T46Unitary
meta import CFSG.LieType.BorelTits.CompleteFlag
meta import CFSG.LieType.Chevalley.C2E6StandardFixedData
meta import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_utab CertificateChecks.KernelU6.Sec3.CL CertificateChecks.KernelU6.Sec3.sL
  CertificateChecks.KernelU6.Sec3.bL

end
