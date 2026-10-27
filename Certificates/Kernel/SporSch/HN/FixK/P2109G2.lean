module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2109Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_2 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS2 FIX2109 2 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2109_2 CFSG.KD.HNXK.fix2109_2 8

end
