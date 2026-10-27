module

public import Certificates.Kernel.FixBoundK.MemData8
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData8
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem8
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix8 fix (fixAt reps gens (nthS [] fx 8)) 0 94

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem8
  CertificateChecks.KernelFixBoundK.FamData8 in
#kc_each CertificateChecks.KernelFixBoundK.Fix8 fam (famAt reps ch fc) 0 94

end
