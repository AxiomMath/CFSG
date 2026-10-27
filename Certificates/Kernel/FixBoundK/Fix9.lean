module

public import Certificates.Kernel.FixBoundK.MemData9
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData9
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem9
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix9 fix (fixAt reps gens (nthS [] fx 9)) 0 35

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem9
  CertificateChecks.KernelFixBoundK.FamData9 in
#kc_each CertificateChecks.KernelFixBoundK.Fix9 fam (famAt reps ch fc) 0 35

end
