module

public import Certificates.Kernel.FixBoundK.MemData7
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData7
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem7
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix7 fix (fixAt reps gens (nthS [] fx 7)) 0 159

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem7
  CertificateChecks.KernelFixBoundK.FamData7 in
#kc_each CertificateChecks.KernelFixBoundK.Fix7 fam (famAt reps ch fc) 0 159

end
