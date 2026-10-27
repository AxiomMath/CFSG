module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import Certificates.Kernel.Misc.YamakiRep.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiRepF

open CFSG.KD.YamakiRep

@[expose] noncomputable def yfHC (q : Nat) : Bool := chunkF RH (rstG RH 12) 14 23040 512 q

end CFSG.KD.YamakiRepF

#kc_slices CFSG.KD.YamakiRepF.yfHK CFSG.KD.YamakiRepF.yfHC 45

end
