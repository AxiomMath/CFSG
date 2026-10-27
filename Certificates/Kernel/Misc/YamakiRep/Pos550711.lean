module

public import Certificates.Data.Kernel.Misc.YamakiGenPos
public import Certificates.Kernel.Misc.YamakiRep.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiGenPos

open CFSG.KD.YamakiRep

@[expose] def posX0 : List Nat := [745, 1498, 868, 778, 15, 1434, 139, 1217, 1137, 759]

@[expose] def posN0 : List Nat := [7552, 7954, 10277, 9101, 350, 10742, 2601, 10743, 10741, 2164, 10592]

@[expose] def posHhat : List Nat :=
  [10356, 1446, 845, 1497, 13197, 22990, 5987, 22841, 22315, 5900, 22206]

theorem ch550711pX : genPosK RX 14 1536 [0, 1, 2, 3, 4, 5, 6, 7, 8, 10] posX0 = true := by
  quickRfl

theorem ch550711pN : genPosK RN 14 10752 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] posN0 = true := by
  quickRfl

theorem ch550711pH : genPosK RH 14 23040 [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11] posHhat = true := by
  quickRfl

end CFSG.KD.YamakiGenPos

end
