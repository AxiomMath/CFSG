module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.M23Mult.P2Data
public import Certificates.Kernel.M23Mult.Words
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.M23MP2

#kb_table CFSG.KBRoute.M23MP2 T1 M23MP2_T1v include_bytes "data/M23MP2_T1v.meta" 2153 3530710806670305831 6618611909121 CertificateChecks.KernelM23Mult.rels6 "1 2 3 4 5"

theorem top : KB.topOk T1.amap (nat_lit 6) = true := by quickRfl

end CFSG.KBRoute.M23MP2

end
