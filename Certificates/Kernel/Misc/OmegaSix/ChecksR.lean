module

public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.RecD
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

@[expose] noncomputable def ch919122R (q : Nat) : Bool := reflChunk ROO 3 51840 RCR 36 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919122RK CFSG.KD.OmegaSix.ch919122R 102

end
