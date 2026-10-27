module

public import Certificates.Kernel.Sporadic.Fi24OrbL.Chain
public import Certificates.Data.Kernel.Spor.Fi24NetPt
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24OrbL

open CFSG.KC.Fi24NetPt CFSG.KD.Fi24Net

@[expose] noncomputable def lvOK : Bool :=
  (List.range 6).all fun i => lv (i + 1) == (lv i).filter fun l => letN NW l (bp i) == bp i

namespace Ck

theorem lv_t : lvOK = true := by quickRfl

end Ck

end CFSG.KD.Fi24OrbL
