module

public import Certificates.Kernel.Th.Rank10508.C2Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.ThRk10508 ch10508cq
  (fun g => CFSG.KC.ThRk10508.cqChunk CFSG.KD.ThM3.RB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThRk10508.Cl g) 0 8

#kc_each CFSG.KD.ThRk10508 ch10508cc
  (fun j => CFSG.KC.ThRk10508.ccK CFSG.KD.ThM3.RB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThRk10508.Cl (CFSG.KC.ThRk10508.getN CFSG.KD.ThRk10508.Cl j)) 0 16

#kc_each CFSG.KD.ThRk10508 ch10508row
  (fun i => CFSG.KC.ThRk10508.rowI CFSG.KD.ThM3.RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    CFSG.KD.ThRk10508.LB CFSG.KD.ThRk10508.Ks CFSG.KD.ThRk10508.Es CFSG.KD.ThRk10508.Ws
    CFSG.KD.ThRk10508.Cl CFSG.KD.ThRk10508.Ds CFSG.KD.ThRk10508.Ts i) 0 12

end
