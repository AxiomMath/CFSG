module

public import Certificates.Data.Kernel.Misc.OmegaSixA
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.RecA
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

@[expose] noncomputable def ch919004O (q : Nat) : Bool :=
  strictY (RO 4) fun xb => cLChunk ROO 3 51840 xb RL 191 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919004OK CFSG.KD.OmegaSix.ch919004O 102

end
