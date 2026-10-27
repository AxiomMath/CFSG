module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2094_2 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2094.GA FIX2094 2 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2094_2 CFSG.KD.HNXK.fix2094_2 8

end
