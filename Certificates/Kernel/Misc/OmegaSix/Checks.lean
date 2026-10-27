module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import Certificates.Kernel.Misc.OmegaSix.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRep CFSG.KD.YamakiRepF

@[expose] noncomputable def oTabC (q : Nat) : Bool := chunkF RO (rstG RO 0) 10 25920 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.oTabK CFSG.KD.OmegaSix.oTabC 51

end
