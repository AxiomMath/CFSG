module

public import Certificates.Kernel.SporSch.HN.FixK.TabS
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2094_0 (k : Nat) : Bool := fixOkS CFSG.KD.HNPt2094.GC SWGC SJGC SGGC FIX2094 0 k

theorem pre2094_0 : CFSG.KC.LL.HNX.sPreOK CFSG.KD.LgHNX.CM3
    (CFSG.KC.LL.HN.subI (CFSG.KD.HNPt2094.EL 0)) SWGC SJGC SGGC SCGC SDGC = true := by
  quickRfl

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2094_0 CFSG.KD.HNXK.fix2094_0 8

end
