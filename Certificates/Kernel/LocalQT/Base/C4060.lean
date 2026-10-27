module

public import Certificates.Kernel.LocalQT.Base.C4060H
public import Certificates.Kernel.LocalQT.Base.C4060P
public import CFSG.Certificates.Kernel.LocalQTRankBSound

public section

namespace CFSG.KD.LQT.C4060

open CFSG.KC.LQT.RB CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.Sporadic.HS.Native (hsData)

theorem cert : RankCert.RankCertS hsData.n hsB (slpTabsA hsTa hsTb hsProg) hsQp 4 hsEnum.1
    hsEnum.2.1 hsEnum.2.2 9 := by
  unfold hsEnum hsSLP
  rw [C4140.n_eq, C4140.ta_eq, C4140.tb_eq]
  exact rankB_sound (by norm_num) _ _ _ _ _ _ 3 _ _ _ _ _ _ _ _ _ _ _ _ hd P.all

end CFSG.KD.LQT.C4060

end
