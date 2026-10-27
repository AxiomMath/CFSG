module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import Certificates.Kernel.Misc.YamakiRep.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiRepF

open CFSG.KD.YamakiRep

@[expose] noncomputable def yfXC (q : Nat) : Bool := chunkF RX (rstG RX 12) 14 1536 512 q

@[expose] noncomputable def yfNC (q : Nat) : Bool := chunkF RN (rstG RN 12) 14 10752 512 q

end CFSG.KD.YamakiRepF

#kc_slices CFSG.KD.YamakiRepF.yfXK CFSG.KD.YamakiRepF.yfXC 3
#kc_slices CFSG.KD.YamakiRepF.yfNK CFSG.KD.YamakiRepF.yfNC 21

end
