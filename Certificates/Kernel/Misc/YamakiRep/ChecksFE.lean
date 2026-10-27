module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import Certificates.Kernel.Misc.YamakiRep.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiRepF

open CFSG.KD.YamakiRep

@[expose] noncomputable def yfEC (q : Nat) : Bool := chunkF RE (rstG RE 12) 14 11520 512 q

end CFSG.KD.YamakiRepF

#kc_slices CFSG.KD.YamakiRepF.yfEK CFSG.KD.YamakiRepF.yfEC 23

end
