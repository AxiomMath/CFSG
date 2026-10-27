module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24ThreeO.gn CFSG.KD.Fi24ThreeO.Ck.gn 0 4
#kc_slice_range CFSG.KD.Fi24ThreeO.fx CFSG.KD.Fi24ThreeO.Ck.fx 0 4
#kc_slice_range CFSG.KD.Fi24ThreeO.cu CFSG.KD.Fi24ThreeO.Ck.cu 0 4

namespace CFSG.KD.Fi24ThreeO.Ck

theorem lv_t : CFSG.KD.Fi24ThreeO.lv = true := by quickRfl

end CFSG.KD.Fi24ThreeO.Ck

end
