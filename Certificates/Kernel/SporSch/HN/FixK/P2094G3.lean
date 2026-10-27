module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2094_3 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2094.G2 FIX2094 3 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2094_3 CFSG.KD.HNXK.fix2094_3 8

end
