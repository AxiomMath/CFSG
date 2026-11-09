module

public import Certificates.Kernel.SporSch.HN.FixK.TabS
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2094_1 (k : Nat) : Bool := fixOkS CFSG.KD.HNPt2094.G4 SWG4 SJG4 SGG4 FIX2094 1 k

theorem pre2094_1 : CFSG.KC.LL.HNX.sPreOK CFSG.KD.LgHNX.CM3
    (CFSG.KC.LL.HN.subI (CFSG.KD.HNPt2094.EL 20)) SWG4 SJG4 SGG4 SCG4 SDG4 = true := by
  quickRfl

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2094_1 CFSG.KD.HNXK.fix2094_1 8

end
