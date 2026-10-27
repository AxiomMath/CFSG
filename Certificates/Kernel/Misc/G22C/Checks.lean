module

public import Certificates.Data.Kernel.Misc.G22C
public import Certificates.Kernel.Misc.G22W.Rec
public import Certificates.Kernel.Misc.G22C.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G22C

open CFSG.KD.G22W

theorem g22c_conj_ok : conjK REC CR 12096 189 = true := by quickRfl

end CFSG.KD.G22C

end
