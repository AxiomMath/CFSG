module

public import Certificates.Data.Foote82OmegaSixAut
public import Certificates.Data.Kernel.Misc.OmegaSixF
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecF
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF

@[expose] noncomputable def ch919150P (q : Nat) : Bool :=
  strictY (RO 1) fun y => pairChunk RO 10 25920 CFSG.CGT.Foote82.OmegaSix.relators y PWF 10 512 q

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919150PK CFSG.KD.OmegaSix.ch919150P 51

end
