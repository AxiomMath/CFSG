module

public import Certificates.Kernel.Sporadic.RawGen
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

#ks_rawchain CertificateChecks.KernelU6.Sec3.CSig 693 10 64 CertificateChecks.KernelU6.Sec3.sSig
  CertificateChecks.KernelU6.Sec3.bSig 2 CertificateChecks.KernelU6.Sec3.dSig

end
