module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2094_1 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2094.G4 FIX2094 1 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2094_1 CFSG.KD.HNXK.fix2094_1 8

end
