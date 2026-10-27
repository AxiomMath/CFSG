module

public import Certificates.Kernel.SmallSpor.M23RData
public import Certificates.Kernel.SporSch.Mathieu.M23Cls
public import Certificates.Data.Kernel.ListBridgeRoot
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSmallSpor.M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ListBridge CFSG.KS.SporSch.MOC

theorem roots : rootsK 23 5 (CertificateChecks.KernelSporSch.M23CK.getD 0 clsD0).R EK.N EK.T WK =
    true := by quickRfl

end CertificateChecks.KernelSmallSpor.M23

end
