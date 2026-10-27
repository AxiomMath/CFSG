module

public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Kernel.Misc.OmegaSix.MaxRec2
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRep

@[expose] noncomputable def ch919005M2 (q : Nat) : Bool := chunkF3 RM2 (rstG RM2 0) 3 25920 256 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919005M2K CFSG.KD.OmegaSix.ch919005M2 102

end
