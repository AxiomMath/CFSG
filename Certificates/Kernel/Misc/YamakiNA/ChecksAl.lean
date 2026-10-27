module

public import Certificates.Data.Kernel.Misc.YamakiNAl
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiNA.RecPos
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.YamakiRep

@[expose] noncomputable def na550822aC (q : Nat) : Bool := cAlChunk RN 14 10752 RX 14 1536 PNX 512 q

theorem na550822b5 : Nat.blt (RN 5) (2 ^ 36) = true := by quickRfl

theorem na550822nA : (!cAlChunk RN 14 10752 RX 14 1536 (fun t => PNX (Nat.add t 1)) 512 0) = true := by
  quickRfl

end CFSG.KD.YamakiNA

#kc_slices CFSG.KD.YamakiNA.na550822aK CFSG.KD.YamakiNA.na550822aC 21

end
