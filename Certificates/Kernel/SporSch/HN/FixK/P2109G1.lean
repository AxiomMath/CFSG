module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2109Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_1 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS1 FIX2109 1 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2109_1 CFSG.KD.HNXK.fix2109_1 8

end
