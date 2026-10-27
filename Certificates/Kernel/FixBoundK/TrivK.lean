module

public import Certificates.Kernel.FixBoundK.TrivData
public import Certificates.Kernel.MonsterB.Perm3018Data
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK.Triv CertificateChecks.KernelFixBoundK.TrivD in
#kc_each CertificateChecks.KernelFixBoundK.TrivK rep (trivAt reps k1s) 0 2

open CFSG.KC.FixBoundK.Triv CertificateChecks.KernelFixBoundK.TrivD in
#kc_each CertificateChecks.KernelFixBoundK.TrivK ws
  (wsAt CertificateChecks.Perm3018.GS CertificateChecks.Perm3018.GA reps ws) 0 16

end
