module

public import Certificates.Kernel.SporSch.HN.FixK.Split
public import Certificates.Kernel.SporSch.HN.Pt2109Data

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_2 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS2 FIX2109 2 k

end CFSG.KD.HNXK

#kss_fix CFSG.KD.HNXK.F2109_2 CFSG.KD.HNXK.fix2109_2 CFSG.KD.HNPt2109.GS2 CFSG.KD.HNXK.FIX2109
  2 0 8 [
  5, 0, 2, 0, 0, 0, 1, 1,
  1, 1, 0, 1, 1, 0, 1, 0,
  0, 0, 1, 2, 2, 1, 0, 0,
  3, 1, 0, 2, 0, 1, 0, 1,
  1, 0, 1, 0, 0, 1, 0, 1,
  1, 2, 2, 0, 1, 2, 2, 4,
  0, 3, 1, 0, 1, 0, 1, 1,
  1, 1, 1, 1, 2, 0, 1, 0]

end
