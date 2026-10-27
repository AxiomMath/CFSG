module

public import Certificates.Data.Kernel.Misc.OmegaSixC
public import Certificates.Kernel.Misc.OmegaSix.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OmegaSix

theorem cntR : Nat.beq (cntK RO 10 25920 (RO 2)) 720 = true := by quickRfl

theorem cntRA : Nat.beq (cntK RO 10 25920 (RO 3)) 576 = true := by quickRfl

theorem cntRB : Nat.beq (cntK RO 10 25920 (RO 4)) 96 = true := by quickRfl

end CFSG.KD.OmegaSix

end
