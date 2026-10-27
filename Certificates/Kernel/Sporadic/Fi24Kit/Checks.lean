module

public import Certificates.Kernel.Sporadic.Fi24Kit.Data
import CFSG.Certificates.Kernel.Common.SliceRange

public section

namespace CFSG.KD.Fi24Kit.Ck

theorem n : CFSG.KD.Fi24Kit.nck = true := by quickRfl

theorem z : CFSG.KD.Fi24Kit.t0 = true := by quickRfl

end CFSG.KD.Fi24Kit.Ck

#kc_slice_range CFSG.KD.Fi24Kit.tck CFSG.KD.Fi24Kit.Ck.t 0 19

end
