module

public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Kernel.Misc.OmegaSix.RecO
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRep

@[expose] noncomputable def ch919122P (q : Nat) : Bool :=
  chunkF3 ROO (rstG ROO 0) 3 51840 256 (Nat.add 102 q)

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919122PK CFSG.KD.OmegaSix.ch919122P 101

end
