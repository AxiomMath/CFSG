module

public import Certificates.Kernel.FixBoundK.MemData0
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData0
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem0
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix0 fix (fixAt reps gens (nthS [] fx 0)) 0 11

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem0
  CertificateChecks.KernelFixBoundK.FamData0 in
#kc_each CertificateChecks.KernelFixBoundK.Fix0 fam (famAt reps ch fc) 0 11

end
