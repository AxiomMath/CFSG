module

public import Certificates.Kernel.PhanD4Dce.CTData
public import Certificates.Data.Kernel.Misc.Coset.ActNet
import CFSG.Certificates.Kernel.Common.Benes

public section

#kc_benes CFSG.KAct.PhanD4CT NTN 0 58 11 fun _ c =>
  CFSG.KC.MonsterConv.Perm.colPlanes (CFSG.KC.MiscCoset.Act.lineL CFSG.KAct.PhanD4CT.A 58 c 1120)
    32 1120 11 0

#kc_select CFSG.KAct.PhanD4CT NT NTN 58

end
