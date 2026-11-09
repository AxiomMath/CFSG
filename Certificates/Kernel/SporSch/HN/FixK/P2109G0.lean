module

public import Certificates.Kernel.SporSch.HN.FixK.Split
public import Certificates.Kernel.SporSch.HN.Pt2109Data

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_0 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS0 FIX2109 0 k

end CFSG.KD.HNXK

#kss_fix CFSG.KD.HNXK.F2109_0 CFSG.KD.HNXK.fix2109_0 CFSG.KD.HNPt2109.GS0 CFSG.KD.HNXK.FIX2109
  0 0 8 [
  14, 10, 11, 7, 8, 9, 6, 16,
  9, 7, 8, 12, 12, 11, 7, 9,
  14, 10, 9, 9, 10, 7, 11, 13,
  11, 8, 10, 9, 11, 7, 8, 6,
  7, 9, 14, 10, 14, 3, 12, 10,
  11, 14, 8, 8, 7, 10, 7, 17,
  9, 11, 9, 12, 13, 9, 14, 11,
  10, 9, 8, 10, 9, 14, 15, 12]

end
