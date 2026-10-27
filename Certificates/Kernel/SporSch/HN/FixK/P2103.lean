module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2103Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2103 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2103.GK1 FIX2103 0 k

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2103 CFSG.KD.HNXK.fix2103 8

end
