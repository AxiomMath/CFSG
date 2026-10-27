module

public import Certificates.Data.Kernel.Misc.OmegaSixMx
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.MaxRec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

@[expose] noncomputable def ch919005W (q : Nat) : Bool :=
  strictY (RO 2) fun r => strictY (RMH 2) fun s₁ => strictY (RMH 3) fun s₂ =>
    cosetChunk RO 10 25920 RMC 2 720 RMW r s₁ s₂ 256 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919005WK CFSG.KD.OmegaSix.ch919005W 102

end
