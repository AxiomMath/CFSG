module

public import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.YModel.Model
public import Certificates.Data.Kernel.Misc.RuCoverNet
public import Certificates.Kernel.Misc.Coset.RuRhoA.Data
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Benes

public section

#kc_repo #kc_nat_items_gz CFSG.KD.RuCoverNet "Certificates/Kernel/Misc/RuCoverNet/data/plan.items.gz" 572 12921841088620272862
  GP_[17] GL_[17] RP_[6] RL_[6] ZP_[2] ZL_[2]

namespace CFSG.KD.RuCoverNet

open CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Misc.RuCoverNet

#kc_select CFSG.KD.RuCoverNet GP GP_ 17
#kc_select CFSG.KD.RuCoverNet GL GL_ 17
#kc_select CFSG.KD.RuCoverNet RP RP_ 6
#kc_select CFSG.KD.RuCoverNet RL RL_ 6
#kc_select CFSG.KD.RuCoverNet ZP ZP_ 2
#kc_select CFSG.KD.RuCoverNet ZL ZL_ 2
#kc_benes CFSG.KD.RuCoverNet U 0 3 14 fun _ g =>
  colPlanes (F CFSG.KAct.RuRho.A (Nat.add (Nat.mul 2 g) 1)) 32 16240 14 0
#kc_benes CFSG.KD.RuCoverNet U 3 17 14 fun T j =>
  netsApply 14 (wid 14) (repU (wid 14) 14) (wordNets 14 6 T (GP (Nat.sub j 3)) (GL (Nat.sub j 3)))
    (idP 14)
#kc_select CFSG.KD.RuCoverNet U U 20

end CFSG.KD.RuCoverNet

end
