module

public import Certificates.Kernel.FixBoundK.MemData5
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData5
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem5
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix5 fix (fixAt reps gens (nthS [] fx 5)) 0 95

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem5
  CertificateChecks.KernelFixBoundK.FamData5 in
#kc_each CertificateChecks.KernelFixBoundK.Fix5 fam (famAt reps ch fc) 0 95

end
