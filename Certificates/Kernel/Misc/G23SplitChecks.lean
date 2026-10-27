module

public import Certificates.Kernel.Misc.G23F3Roots
public import Certificates.Data.G23Emb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G23F3

open CFSG.KC.Ord CFSG.KC.Misc.G23F3 CFSG.CGT.PushingUpLit.CGT6.EmbModule

theorem split_ok :
    andB constsK (splitK (SK uW) (SK vW) (SK z0W) (SK a1W) (SK a2W) (SK cW)) = true := by
  quickRfl

end CFSG.KD.Misc.G23F3

end
