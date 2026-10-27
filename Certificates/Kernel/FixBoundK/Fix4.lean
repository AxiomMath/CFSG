module

public import Certificates.Kernel.FixBoundK.MemData4
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData4
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem4
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix4 fix (fixAt reps gens (nthS [] fx 4)) 0 133

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem4
  CertificateChecks.KernelFixBoundK.FamData4 in
#kc_each CertificateChecks.KernelFixBoundK.Fix4 fam (famAt reps ch fc) 0 133

end
