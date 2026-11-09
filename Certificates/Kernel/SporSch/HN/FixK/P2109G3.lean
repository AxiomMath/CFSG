module

public import Certificates.Kernel.SporSch.HN.FixK.Split
public import Certificates.Kernel.SporSch.HN.Pt2109Data

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2109_3 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2109.GS3 FIX2109 3 k

end CFSG.KD.HNXK

#kss_fix CFSG.KD.HNXK.F2109_3 CFSG.KD.HNXK.fix2109_3 CFSG.KD.HNPt2109.GS3 CFSG.KD.HNXK.FIX2109
  3 0 8 [
  17, 10, 7, 14, 11, 12, 10, 12,
  8, 10, 10, 7, 7, 10, 10, 16,
  9, 10, 5, 17, 12, 13, 11, 11,
  10, 12, 7, 10, 13, 15, 10, 12,
  12, 6, 13, 5, 8, 7, 6, 5,
  9, 7, 7, 18, 8, 11, 9, 9,
  4, 9, 9, 8, 13, 5, 12, 8,
  12, 9, 13, 6, 13, 12, 10, 14]

end
