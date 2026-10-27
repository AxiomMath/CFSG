module

public import Certificates.Data.Kernel.Misc.YamakiNW
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiA0.Rec
public import Certificates.Kernel.Misc.YamakiNA.RecPosH
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.YamakiRep

theorem na550822w : wK CFSG.KD.YamakiA0.REC = true := by quickRfl

@[expose] noncomputable def na550822sC (q : Nat) : Bool := stabChunk RH 14 23040 RX 14 1536 PHX 512 q

@[expose] noncomputable def na550822rC (q : Nat) : Bool :=
  rhoChunk RN 14 10752 CFSG.KD.YamakiA0.REC 512 q

theorem na550822nW : (!wK RH) = true := by quickRfl

theorem na550822nS :
    (!stabChunk RH 14 23040 RX 14 1536 (fun t => PHX (Nat.add t 1)) 512 0) = true := by
  quickRfl

theorem na550822nR : (!rhoChunk RN 14 10752 RH 512 0) = true := by quickRfl

end CFSG.KD.YamakiNA

#kc_slices CFSG.KD.YamakiNA.na550822sK CFSG.KD.YamakiNA.na550822sC 45

#kc_slices CFSG.KD.YamakiNA.na550822rK CFSG.KD.YamakiNA.na550822rC 21

end
