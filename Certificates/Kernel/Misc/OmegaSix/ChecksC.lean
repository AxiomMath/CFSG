module

public import Certificates.Data.Kernel.Misc.OmegaSixK
public import Certificates.Kernel.Misc.OmegaSix.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

@[expose] noncomputable def oClosC (q : Nat) : Bool :=
  strictY (RO 3) fun y => strictY (RO 8) fun e₁ => strictY (RO 9) fun e₂ =>
    closChunk RO 10 25920 y e₁ e₂ 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.oClosK CFSG.KD.OmegaSix.oClosC 51

end
