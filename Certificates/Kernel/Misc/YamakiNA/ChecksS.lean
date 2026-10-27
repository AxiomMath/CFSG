module

public import Certificates.Data.Kernel.Misc.YamakiNS
public import Certificates.Kernel.Misc.YamakiS0.Rec
public import Certificates.Kernel.Misc.YamakiA0.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiNA

@[expose] noncomputable def na550822yC (q : Nat) : Bool :=
  sylChunk CFSG.KD.YamakiS0.REC CFSG.KD.YamakiA0.REC 32 q

theorem na550822nY :
    (!sylChunk (fun j => CFSG.KD.YamakiA0.REC j) CFSG.KD.YamakiS0.REC 32 0) = true := by
  quickRfl

end CFSG.KD.YamakiNA

#kc_slices CFSG.KD.YamakiNA.na550822yK CFSG.KD.YamakiNA.na550822yC 16

end
