module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.Sec3.Arrs
meta import Certificates.Kernel.UnitarySix.Sec3.Arrs
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

#ks_rawchain CertificateChecks.KernelU6.Sec3.CX3 693 10 64 CertificateChecks.KernelU6.Sec3.sX3
  CertificateChecks.KernelU6.Sec3.bX3 1 CertificateChecks.KernelU6.Sec3.dX3

end
