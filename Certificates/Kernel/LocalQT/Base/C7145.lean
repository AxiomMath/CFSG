module

public import Certificates.Kernel.LocalQT.Base.C7145H
public import Certificates.Kernel.LocalQT.Base.C7145N
public import CFSG.Certificates.Kernel.LocalQTTreeTSound

public section

namespace CFSG.KD.LQT.C7145

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGRank

theorem tree : treeCheck m24Enum.1.size m24Qp.length m24Qp.length m24Enum.2.1 m24Enum.2.2 129
    #[] = true := by
  unfold m24Enum m24SLP
  exact CFSG.KC.LQT.TT.treeT_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd N.all

end CFSG.KD.LQT.C7145

end
