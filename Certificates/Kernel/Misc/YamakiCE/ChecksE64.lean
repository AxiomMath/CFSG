module

public import Certificates.Data.Kernel.Misc.YamakiE64
public import Certificates.Kernel.Misc.YamakiS0.Rec
public import Certificates.Kernel.Misc.YamakiA0.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiE64

@[expose] noncomputable def ce550823eC (q : Nat) : Bool :=
  e64Chunk CFSG.KD.YamakiS0.REC 9 CFSG.KD.YamakiA0.REC 12 32 q

end CFSG.KD.YamakiE64

#kc_slices CFSG.KD.YamakiE64.ce550823eK CFSG.KD.YamakiE64.ce550823eC 16

end
