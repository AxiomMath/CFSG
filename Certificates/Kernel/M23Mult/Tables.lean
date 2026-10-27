module

public import Certificates.Data.Kernel.Bounds.Table
public import Certificates.Kernel.M23Mult.P2Route
public import Certificates.Kernel.M23Mult.P1Route
public import Certificates.Kernel.M23Mult.C2Route
public import Certificates.Kernel.M23Mult.C1Route
import Certificates.Kernel.Bounds.Assemble
import Certificates.Kernel.M23Mult.P2K0
import Certificates.Kernel.M23Mult.P1K0
import Certificates.Kernel.M23Mult.C2K0
import Certificates.Kernel.M23Mult.C1K0
import Certificates.Kernel.M23Mult.C1K1

public section

#kb_cert CFSG.KBRoute.M23MP2 T1 M23MP2_T1v include_bytes "data/M23MP2_T1v.meta" 2153 3530710806670305831 CertificateChecks.KernelM23Mult.rels6
#kb_cert CFSG.KBRoute.M23MP1 T1 M23MP1_T1v include_bytes "data/M23MP1_T1v.meta" 5636 7221468635155766762 CertificateChecks.KernelM23Mult.rels5
#kb_cert CFSG.KBRoute.M23MC2 T1 M23MC2_T1v include_bytes "data/M23MC2_T1v.meta" 4139 11757060361876678576 CertificateChecks.KernelM23Mult.cover6
#kb_cert CFSG.KBRoute.M23MC1 T1 M23MC1_T1v include_bytes "data/M23MC1_T1v.meta" 8809 15296935670973712761 CertificateChecks.KernelM23Mult.cover5

namespace CertificateChecks.KernelM23Mult

theorem p2 : CFSG.KBRoute.M23MP2.T1.ok = true := by kb_assemble M23MP2_T1v

theorem p1 : CFSG.KBRoute.M23MP1.T1.ok = true := by kb_assemble M23MP1_T1v

theorem c2 : CFSG.KBRoute.M23MC2.T1.ok = true := by kb_assemble M23MC2_T1v

theorem c1 : CFSG.KBRoute.M23MC1.T1.ok = true := by kb_assemble M23MC1_T1v

end CertificateChecks.KernelM23Mult

end
