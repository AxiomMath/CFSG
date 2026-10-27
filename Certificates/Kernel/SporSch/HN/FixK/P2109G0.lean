module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2109Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_0 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS0 FIX2109 0 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2109_0 CFSG.KD.HNXK.fix2109_0 8

end
