module

public import Certificates.Data.Kernel.Misc.OmegaSixC
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecC
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

theorem cHdrA : hdrC RCA (RO 0) (RO 1) (RCA 4) = true := by quickRfl

theorem cHdrB : hdrC RCB (RO 0) (RO 1) (RCB 4) = true := by quickRfl

theorem cRootA : RCA 4 = RO 3 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem cRootB : RCB 4 = RO 4 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem cHeadA : headC RCA 5 45 = true := by quickRfl

theorem cHeadB : headC RCB 5 270 = true := by quickRfl

@[expose] noncomputable def ch919121A (q : Nat) : Bool := chunkF RCA (cjG RCA) 5 45 32 q

@[expose] noncomputable def ch919121B (q : Nat) : Bool := chunkF RCB (cjG RCB) 5 270 32 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919121AK CFSG.KD.OmegaSix.ch919121A 2
#kc_slices CFSG.KD.OmegaSix.ch919121BK CFSG.KD.OmegaSix.ch919121B 9

end
