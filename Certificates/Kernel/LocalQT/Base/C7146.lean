module

public import Certificates.Kernel.LocalQT.Base.C7146H
public import CFSG.Certificates.Kernel.LocalQTTreeTSound
public import Certificates.Kernel.LocalQT.Base.C4141

public section

namespace CFSG.KD.LQT.C7146

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGRank

theorem tree : treeCheck heEnum.1.size heQp.length heQp.length heEnum.2.1 heEnum.2.2 5 #[] =
    true := by
  unfold heEnum heSLP
  rw [C4141.ta_eq, C4141.tb_eq]
  exact CFSG.KC.LQT.TT.treeT_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd
    C4141.N.all

end CFSG.KD.LQT.C7146

end
