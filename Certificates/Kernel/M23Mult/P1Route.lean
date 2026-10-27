module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.M23Mult.P1Data
public import Certificates.Kernel.M23Mult.Words
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.M23MP1

#kb_table CFSG.KBRoute.M23MP1 T1 M23MP1_T1v include_bytes "data/M23MP1_T1v.meta" 5636 7221468635155766762 21542142465 CertificateChecks.KernelM23Mult.rels5 ""

theorem top : KB.topOk T1.amap (nat_lit 5) = true := by quickRfl

end CFSG.KBRoute.M23MP1

end
