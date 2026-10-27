module

public import Certificates.Kernel.FixBoundK.MemData6
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData6
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem6
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix6 fix (fixAt reps gens (nthS [] fx 6)) 0 72

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem6
  CertificateChecks.KernelFixBoundK.FamData6 in
#kc_each CertificateChecks.KernelFixBoundK.Fix6 fam (famAt reps ch fc) 0 72

end
