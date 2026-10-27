module

public import Certificates.Data.Kernel.Misc.YamakiNA
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiA0.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.YamakiRep

@[expose] noncomputable def na550822cC (q : Nat) : Bool :=
  cA0Chunk RH 14 23040 CFSG.KD.YamakiA0.REC 512 q

theorem na550822nm : normA0K CFSG.KD.YamakiA0.REC = true := by quickRfl

theorem na550822sv : sevenK CFSG.KD.YamakiA0.REC = true := by quickRfl

theorem na550822ac : alphaClassK CFSG.KD.YamakiA0.REC = true := by quickRfl

theorem na550822nC : (!cA0Chunk RH 14 23040 RH 512 0) = true := by quickRfl

theorem na550822nN : (!normA0K RH) = true := by quickRfl

end CFSG.KD.YamakiNA

#kc_slices CFSG.KD.YamakiNA.na550822cK CFSG.KD.YamakiNA.na550822cC 45

end
