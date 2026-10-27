module

public import Certificates.Data.Kernel.Misc.YamakiCE
public import Certificates.Kernel.Misc.YamakiRep.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiCE

open CFSG.KD.YamakiRep

@[expose] noncomputable def ce550823cC (q : Nat) : Bool := centChunk RH 14 23040 512 q 5

end CFSG.KD.YamakiCE

#kc_slices CFSG.KD.YamakiCE.ce550823cK CFSG.KD.YamakiCE.ce550823cC 45

end
