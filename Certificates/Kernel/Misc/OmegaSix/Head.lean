module

public import Certificates.Data.Kernel.Misc.OmegaSixK
public import Certificates.Data.Kernel.Misc.YamakiGenPos
public import Certificates.Kernel.Misc.OmegaSix.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRep CFSG.KD.YamakiGenPos

theorem oHead : headK RO 10 25920 2 = true := by quickRfl

theorem oHdrLt : ∀ j < 10, RO j < 2 ^ 36 := by decide +kernel

theorem oCent1 : centInvK (RO 3) (RO 8) = true := by quickRfl

theorem oCent2 : centInvK (RO 3) (RO 9) = true := by quickRfl

theorem oPos : genPosK RO 10 25920 [8, 9] [ROP 8, ROP 9] = true := by quickRfl

end CFSG.KD.OmegaSix

end
