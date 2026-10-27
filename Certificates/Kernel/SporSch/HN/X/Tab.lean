module

public import CFSG.Certificates.Kernel.Local.HN.X.Lib
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_root CertificateChecks.KernelSporSch.HNX.CNT
  "Certificates/Kernel/SporSch/HN/data/hnx_cnt.bin" 89065 14973375550631926732
#kc_repo #kc_items_root CertificateChecks.KernelSporSch.HNX.SGT
  "Certificates/Kernel/SporSch/HN/data/hnx_sgt.bin" 3116129 1989065047676969988

public noncomputable section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] def coreOk (q : Nat) : Bool :=
  Nat.beq (coreLeaf TX 464 1140000 MS CM3 M GA GB q (hnxC q)) (HNX.CNT q)

@[expose] def sortOk (q : Nat) : Bool := sortChunk TX 464 1140000 (HNX.SGT q) (hnxS q)

end CFSG.KD.HNXK

end
