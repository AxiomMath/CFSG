module

public import Certificates.Kernel.Sporadic.Fi24G2e.RData
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

#kc_repo #kc_natLines CFSG.KD.Fi24G2e ZPA "Certificates/Kernel/Sporadic/Fi24G2e/data/zpA.txt" 63 14713123379320909823
#kc_repo #kc_natLines CFSG.KD.Fi24G2e ZPB "Certificates/Kernel/Sporadic/Fi24G2e/data/zpB.txt" 63 13352709250624936076
#kc_repo #kc_natLines CFSG.KD.Fi24G2e ZPC "Certificates/Kernel/Sporadic/Fi24G2e/data/zpC.txt" 63 3927589160042856505
#kc_repo #kc_natLines CFSG.KD.Fi24G2e ZFA "Certificates/Kernel/Sporadic/Fi24G2e/data/zfA.txt" 21 5485341194807919378
#kc_repo #kc_natLines CFSG.KD.Fi24G2e ZFB "Certificates/Kernel/Sporadic/Fi24G2e/data/zfB.txt" 21 17452768616725290424

#kc_select CFSG.KD.Fi24G2e ZPAs ZPA.n 21
#kc_select CFSG.KD.Fi24G2e ZPBs ZPB.n 21
#kc_select CFSG.KD.Fi24G2e ZPCs ZPC.n 21
#kc_select CFSG.KD.Fi24G2e ZFAs ZFA.n 7
#kc_select CFSG.KD.Fi24G2e ZFBs ZFB.n 7

public noncomputable section

namespace CFSG.KD.Fi24G2e

@[expose] def zpC (s : Nat) : Bool :=
  Nat.beq (CFSG.KD.BrFi24.MUL (RX (ZPAs s)) (RX (ZPBs s))) (RX (ZPCs s))

@[expose] def zfC (i : Nat) : Bool :=
  Nat.beq (CFSG.KD.BrFi24.MUL (RX (ZFAs i)) (RX (ZFBs i))) CFSG.KD.BrFi24.ONE

end CFSG.KD.Fi24G2e

#kss_each CFSG.KD.Fi24G2e.RZ.P CFSG.KD.Fi24G2e.zpC 21

#kss_each CFSG.KD.Fi24G2e.RZ.F CFSG.KD.Fi24G2e.zfC 7

end
