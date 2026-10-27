module

public import Certificates.Kernel.FixBoundK.MemData2
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData2
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem2
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix2 fix (fixAt reps gens (nthS [] fx 2)) 0 56

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem2
  CertificateChecks.KernelFixBoundK.FamData2 in
#kc_each CertificateChecks.KernelFixBoundK.Fix2 fam (famAt reps ch fc) 0 56

end
