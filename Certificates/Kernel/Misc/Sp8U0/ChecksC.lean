module

public import Certificates.Data.Kernel.Misc.Sp8U0
public import Certificates.Kernel.Misc.Sp8U0.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8U0

open CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KD.Sp8Syl3 CFSG.KC.Mat8P

theorem u06_start : Nat.beq (recX REC 9 0) oneP = true := by quickRfl

theorem u06_counts :
    (Nat.beq (recCW REC 9 5 0) 1 && Nat.beq (recCW REC 9 5 327680) 65536) = true := by
  quickRfl

theorem u06_zu_ok : zuK REC = true := by quickRfl

end CFSG.KD.Sp8U0

end
