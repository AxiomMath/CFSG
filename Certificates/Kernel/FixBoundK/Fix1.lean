module

public import Certificates.Kernel.FixBoundK.MemData1
public import Certificates.Kernel.FixBoundK.FixData
public import Certificates.Kernel.FixBoundK.FamData1
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem1
  CertificateChecks.KernelFixBoundK.FixData in
#kc_each CertificateChecks.KernelFixBoundK.Fix1 fix (fixAt reps gens (nthS [] fx 1)) 0 31

open CFSG.KC.FixBoundK CertificateChecks.KernelFixBoundK.Mem1
  CertificateChecks.KernelFixBoundK.FamData1 in
#kc_each CertificateChecks.KernelFixBoundK.Fix1 fam (famAt reps ch fc) 0 31

end
