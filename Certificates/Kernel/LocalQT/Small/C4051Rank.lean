module

public import Certificates.Data.Kernel.LocalQT.SixRank
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4051

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.X6

theorem hrank : rankOK = true := by quickRfl

theorem nrank1 : notB (allP 6 fun x => Nat.beq (unrank6 (Nat.add (rank6 x) 1)) x) = true := by
  quickRfl

theorem nrank2 : notB (Nat.beq (unrank6 (rank6 (one 6))) (mul 6 (swap 6 0 1) (one 6))) = true := by
  quickRfl

end CFSG.KD.LQT.C4051

end
