module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.M23Mult.C2Data
public import Certificates.Kernel.M23Mult.Words
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.M23MC2

#kb_table CFSG.KBRoute.M23MC2 T1 M23MC2_T1v include_bytes "data/M23MC2_T1v.meta" 4139 11757060361876678576 6618611909121 CertificateChecks.KernelM23Mult.cover6 "1 2 3 4 5"

theorem top : KB.topOk T1.amap (nat_lit 6) = true := by quickRfl

end CFSG.KBRoute.M23MC2

end
