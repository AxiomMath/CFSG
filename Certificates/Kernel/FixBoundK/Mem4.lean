module

public import Certificates.Kernel.FixBoundK.MemData4
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem4 in
#kc_each CertificateChecks.KernelFixBoundK.Mem4 rep (repAt reps) 0 133

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem4 in
#kc_each CertificateChecks.KernelFixBoundK.Mem4 ch (chAt reps ch) 0 350

end
