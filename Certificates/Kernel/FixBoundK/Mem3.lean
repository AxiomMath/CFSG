module

public import Certificates.Kernel.FixBoundK.MemData3
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem3 in
#kc_each CertificateChecks.KernelFixBoundK.Mem3 rep (repAt reps) 0 65

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem3 in
#kc_each CertificateChecks.KernelFixBoundK.Mem3 ch (chAt reps ch) 0 280

end
