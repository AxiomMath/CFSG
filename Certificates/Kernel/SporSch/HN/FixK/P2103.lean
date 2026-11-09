module

public import Certificates.Kernel.SporSch.HN.FixK.Split
public import Certificates.Kernel.SporSch.HN.Pt2103Data

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2103 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2103.GK1 FIX2103 0 k

end CFSG.KD.HNXK

#kss_fix CFSG.KD.HNXK.F2103 CFSG.KD.HNXK.fix2103 CFSG.KD.HNPt2103.GK1 CFSG.KD.HNXK.FIX2103
  0 0 8 [
  2, 0, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0, 0, 0, 0, 0, 1]

end
