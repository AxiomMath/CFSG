module

public import Certificates.Kernel.FixBoundK.PairData
public import Certificates.Kernel.FixBoundK.PairGData
public import Certificates.Kernel.MonsterB.Perm3018Data
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK.Pair CFSG.KC.SortTree CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.PairD in
#kc_each CertificateChecks.KernelFixBoundK.Pair3 src
  (srcAt IV RG CM B nB 1024 751 191 (recT CertificateChecks.Perm3018.S 6 140) lo src) 564 752

end
