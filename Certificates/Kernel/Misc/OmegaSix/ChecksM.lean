module

public import Certificates.Data.Kernel.Misc.OmegaSixC
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecC
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

@[expose] noncomputable def ch919121M (q : Nat) : Bool :=
  clsChunk RO 10 25920 RCA 45 RCB 270 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919121MK CFSG.KD.OmegaSix.ch919121M 51

end
