module

public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Data.Kernel.Misc.OmegaSixK
public import Certificates.Data.Kernel.Misc.YamakiGenPos
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecC
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.RecD
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRep CFSG.KD.YamakiRepF CFSG.KD.YamakiGenPos

theorem oHeadO : headK ROO 3 51840 3 = true := by quickRfl

theorem oGen0 : ROO 0 = RO 0 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem oGen1 : ROO 1 = RO 1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem oGen2 : ROO 2 = RO 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem rRoot : RCR 4 = ROO 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem rHdr : hdrC RCR (ROO 0) (ROO 1) (RCR 4) = true := by quickRfl

theorem rHead : headC RCR 5 36 = true := by quickRfl

@[expose] noncomputable def ch919122C (q : Nat) : Bool := chunkF RCR (cjG RCR) 5 36 32 q

theorem wGen0 : RW 0 = commK (RO 5) (RO 6) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem wGen1 : RW 1 = commK (RO 5) (RO 7) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem wHead : headK RW 2 360 2 = true := by quickRfl

theorem wTab : chunkF RW (rstG RW 0) 2 360 512 0 = true := by quickRfl

theorem wCls : clsChunk RW 2 360 RCB 270 RCB 270 512 0 = true := by quickRfl

theorem oCent5 : centInvK (RO 2) (RO 5) = true := by quickRfl

theorem oCent6 : centInvK (RO 2) (RO 6) = true := by quickRfl

theorem oCent7 : centInvK (RO 2) (RO 7) = true := by quickRfl

theorem oPosC : genPosK RO 10 25920 [5, 6, 7] [ROP 5, ROP 6, ROP 7] = true := by quickRfl

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919122CK CFSG.KD.OmegaSix.ch919122C 2

end
