module

public import Certificates.Kernel.FixBoundK.MemData6
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem6 in
#kc_each CertificateChecks.KernelFixBoundK.Mem6 rep (repAt reps) 0 72

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem6 in
#kc_each CertificateChecks.KernelFixBoundK.Mem6 ch (chAt reps ch) 0 308

end
