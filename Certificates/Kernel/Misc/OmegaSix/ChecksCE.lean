module

public import Certificates.Data.Kernel.Misc.OmegaSixA
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecA
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

@[expose] noncomputable def ch919004E (q : Nat) : Bool :=
  strictY (RO 3) fun xa => strictY (RO 4) fun xb => centChunk RO 10 25920 xa xb RL 191 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919004EK CFSG.KD.OmegaSix.ch919004E 51

end
