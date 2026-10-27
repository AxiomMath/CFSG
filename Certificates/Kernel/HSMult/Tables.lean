module

public import Certificates.Data.Kernel.Bounds.Table
public import Certificates.Kernel.HSMult.P2Route
public import Certificates.Kernel.HSMult.C2Route
import Certificates.Kernel.Bounds.Assemble
import Certificates.Kernel.HSMult.P2K0
import Certificates.Kernel.HSMult.P2K1
import Certificates.Kernel.HSMult.C2K0
import Certificates.Kernel.HSMult.C2K1
import Certificates.Kernel.HSMult.C2K2
import Certificates.Kernel.HSMult.C2K3
import Certificates.Kernel.HSMult.C2K4
import Certificates.Kernel.HSMult.C2K5
import Certificates.Kernel.HSMult.C2K6

public section

#kb_cert CFSG.KBRoute.HSMP2 T1 HSMP2_T1v include_bytes "data/HSMP2_T1v.meta" 10434 16526001543835221162 CertificateChecks.KernelHSMult.rels6
#kb_cert CFSG.KBRoute.HSMC2 T1 HSMC2_T1v include_bytes "data/HSMC2_T1v.meta" 40411 9787343173744834628 CertificateChecks.KernelHSMult.cover6

namespace CertificateChecks.KernelHSMult

theorem p2 : CFSG.KBRoute.HSMP2.T1.ok = true := by kb_assemble HSMP2_T1v

theorem c2 : CFSG.KBRoute.HSMC2.T1.ok = true := by kb_assemble HSMC2_T1v

end CertificateChecks.KernelHSMult

end
