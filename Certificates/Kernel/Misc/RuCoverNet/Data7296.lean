module

public import Certificates.Kernel.Misc.RuCoverNet.Data
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Benes

public section

#kc_repo #kc_nat_items_gz CFSG.KD.RuCoverNet7296 "Certificates/Kernel/Misc/RuCoverNet/data/plan7296.items.gz" 6800 8808749326982422261
  CP_[20] CL_[20] MC_[80] NB_[64] NX_[64] NY_[64] KI_[256] KB_[256] KX_[256] KY_[256]

namespace CFSG.KD.RuCoverNet7296

open CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

#kc_select CFSG.KD.RuCoverNet7296 CP CP_ 20
#kc_select CFSG.KD.RuCoverNet7296 CL CL_ 20
#kc_select CFSG.KD.RuCoverNet7296 MC MC_ 80
#kc_select CFSG.KD.RuCoverNet7296 NB NB_ 64
#kc_select CFSG.KD.RuCoverNet7296 NX NX_ 64
#kc_select CFSG.KD.RuCoverNet7296 NY NY_ 64
#kc_select CFSG.KD.RuCoverNet7296 KI KI_ 256
#kc_select CFSG.KD.RuCoverNet7296 KB KB_ 256
#kc_select CFSG.KD.RuCoverNet7296 KX KX_ 256
#kc_select CFSG.KD.RuCoverNet7296 KY KY_ 256
@[expose] noncomputable def V0 : Nat := CFSG.KD.RuCoverNet.U3
@[expose] noncomputable def V1 : Nat := CFSG.KD.RuCoverNet.U4
#kc_benes CFSG.KD.RuCoverNet7296 V 2 20 14 fun T j =>
  netsApply 14 (wid 14) (repU (wid 14) 14) (wordNets 14 6 T (CP (Nat.sub j 2)) (CL (Nat.sub j 2)))
    (idP 14)
#kc_select CFSG.KD.RuCoverNet7296 V V 22

end CFSG.KD.RuCoverNet7296

end
