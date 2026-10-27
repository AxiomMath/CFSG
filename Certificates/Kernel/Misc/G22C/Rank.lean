module

public import Certificates.Data.Kernel.Misc.G22C
public import Certificates.Kernel.Misc.G22W.Rec
public import Certificates.Kernel.Misc.G22C.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G22C

open CFSG.KD.G22W

theorem g22c_class0_ok : classK REC CR 12096 false = true := by quickRfl

theorem g22c_class1_ok : classK REC CR 12096 true = true := by quickRfl

theorem g22c_rank0_ok : rankK REC CR 12096 false = true := by quickRfl

theorem g22c_rank1_ok : rankK REC CR 12096 true = true := by quickRfl

end CFSG.KD.G22C

end
