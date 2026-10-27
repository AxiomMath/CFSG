module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.M23Mult.C1Data
public import Certificates.Kernel.M23Mult.Words
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.M23MC1

#kb_table CFSG.KBRoute.M23MC1 T1 M23MC1_T1v include_bytes "data/M23MC1_T1v.meta" 8809 15296935670973712761 21542142465 CertificateChecks.KernelM23Mult.cover5 ""

theorem top : KB.topOk T1.amap (nat_lit 5) = true := by quickRfl

end CFSG.KBRoute.M23MC1

end
