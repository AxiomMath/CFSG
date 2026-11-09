module

public import Certificates.Kernel.SporSch.HN.FixK.Split
public import Certificates.Kernel.SporSch.HN.Pt2109Data

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_1 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS1 FIX2109 1 k

end CFSG.KD.HNXK

#kss_fix CFSG.KD.HNXK.F2109_1 CFSG.KD.HNXK.fix2109_1 CFSG.KD.HNPt2109.GS1 CFSG.KD.HNXK.FIX2109
  1 0 8 [
  10, 11, 12, 9, 9, 13, 11, 7,
  15, 7, 14, 7, 13, 7, 12, 6,
  13, 7, 8, 12, 13, 11, 13, 10,
  7, 12, 7, 8, 13, 18, 5, 13,
  7, 8, 15, 13, 5, 9, 7, 5,
  10, 9, 8, 8, 13, 11, 8, 8,
  12, 9, 12, 15, 10, 9, 11, 9,
  11, 9, 15, 5, 12, 9, 9, 11]

end
