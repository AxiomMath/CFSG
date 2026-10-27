module

public import Certificates.Kernel.FixBoundK.MemData8
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem8 in
#kc_each CertificateChecks.KernelFixBoundK.Mem8 rep (repAt reps) 0 94

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem8 in
#kc_each CertificateChecks.KernelFixBoundK.Mem8 ch (chAt reps ch) 0 330

end
