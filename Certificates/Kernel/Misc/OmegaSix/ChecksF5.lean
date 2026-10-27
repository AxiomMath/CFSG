module

public import Certificates.Data.Kernel.Misc.OmegaSixF
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecF
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

@[expose] noncomputable def ch919150F (q : Nat) : Bool := fiveChunk RO 10 25920 RCF 5184 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919150FK CFSG.KD.OmegaSix.ch919150F 51

end
