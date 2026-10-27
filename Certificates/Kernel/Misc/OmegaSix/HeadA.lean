module

public import Certificates.Data.Foote82OmegaSixCent
public import Certificates.Data.Kernel.Misc.OmegaSixA
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecC
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.RecA
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep CFSG.KD.YamakiRepF

theorem reflCheck_ok : reflCheck () = true := by decide +kernel

theorem aHdrA : hdrO RCA3 (ROO 0) (ROO 1) (ROO 2) (RO 3) = true := by quickRfl

theorem aHdrB : hdrO RCB3 (ROO 0) (ROO 1) (ROO 2) (RO 4) = true := by quickRfl

theorem aHeadA : headC3 RCA3 5 45 = true := by quickRfl

theorem aHeadB : headC3 RCB3 5 270 = true := by quickRfl

theorem aOrbA : chunkF3 RCA3 (cjO ROO RCA3) 5 45 512 0 = true := by quickRfl

theorem aOrbB : chunkF3 RCB3 (cjO ROO RCB3) 5 270 512 0 = true := by quickRfl

theorem aSubA : subOrbK RCA 45 RCA3 45 = true := by quickRfl

theorem aSubB : subOrbK RCB 270 RCB3 270 = true := by quickRfl

theorem aRepA : memK RO 10 25920 (RO 3) = true := by quickRfl

theorem aRepB : memK RO 10 25920 (RO 4) = true := by quickRfl

end CFSG.KD.OmegaSix

end
