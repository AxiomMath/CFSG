module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24ThreeO.ct CFSG.KD.Fi24ThreeO.Ck.ct 0 26
#kc_slice_range CFSG.KD.Fi24ThreeO.cst CFSG.KD.Fi24ThreeO.Ck.cst 0 3
#kc_slice_range CFSG.KD.Fi24ThreeO.bs CFSG.KD.Fi24ThreeO.Ck.bs 0 6

namespace CFSG.KD.Fi24ThreeO.Ck

theorem bg_t : CFSG.KD.Fi24ThreeO.bg = true := by quickRfl

end CFSG.KD.Fi24ThreeO.Ck

end
