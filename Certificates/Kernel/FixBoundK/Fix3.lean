module

public import Certificates.Kernel.FixBoundK.MemData3
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData3
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem3
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix3 fix (fixAt reps gens (nthS [] fx 3)) 0 65

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem3
  CertificateChecks.KernelFixBoundK.FamData3 in
#kc_each CertificateChecks.KernelFixBoundK.Fix3 fam (famAt reps ch fc) 0 65

end
