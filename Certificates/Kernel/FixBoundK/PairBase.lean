module

public import Certificates.Kernel.FixBoundK.PairGData
public import Certificates.Kernel.MonsterB.Perm3018Data
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

@[expose] public section

open CFSG.KC.FixBoundK.Pair CFSG.KC.SortTree CertificateChecks.KernelFixBoundK.PairG in
#kc_each CertificateChecks.KernelFixBoundK.PairBase inv
  (invOK IV IR (recT CertificateChecks.Perm3018.S 6 140) 191) 0 191

open CFSG.KC.FixBoundK.Pair CFSG.KC.SortTree CFSG.KLie.CT
  CertificateChecks.KernelFixBoundK.PairG in
#kc_each CertificateChecks.KernelFixBoundK.PairBase base
  (fun c => allN 64 fun l => baseOK B nB (recT CertificateChecks.Perm3018.S 6 140) (64 * c + l))
  0 16

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG in
#kc_each CertificateChecks.KernelFixBoundK.PairBase cm (cmOK IV CM B nB 191) 0 191

end
