module

public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Data
import CFSG.Certificates.Kernel.Common.SliceRange

public section

namespace CFSG.KD.Fi24ThreeAK.Ck

theorem cov_t : CFSG.KD.Fi24ThreeAK.cov = true := by quickRfl

theorem line_t : CFSG.KD.Fi24ThreeAK.line = true := by quickRfl

theorem mv_t : CFSG.KD.Fi24ThreeAK.mv = true := by quickRfl

theorem fix_t : CFSG.KD.Fi24ThreeAK.fix = true := by quickRfl

end CFSG.KD.Fi24ThreeAK.Ck

#kc_slice_range CFSG.KD.Fi24ThreeAK.fl CFSG.KD.Fi24ThreeAK.Ck.f 0 5
#kc_slice_range CFSG.KD.Fi24ThreeAK.cj CFSG.KD.Fi24ThreeAK.Ck.c 0 6

end
