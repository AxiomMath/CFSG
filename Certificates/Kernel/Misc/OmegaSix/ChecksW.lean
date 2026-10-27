module

public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.RecD
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

@[expose] noncomputable def ch919122W (q : Nat) : Bool :=
  strictY (RW 0) fun w₁ => strictY (RW 1) fun w₂ => strictY (ROO 2) fun r =>
    a6cChunk ROO 3 51840 w₁ w₂ r 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919122WK CFSG.KD.OmegaSix.ch919122W 102

end
