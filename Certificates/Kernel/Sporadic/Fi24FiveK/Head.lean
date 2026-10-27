module

public import Certificates.Kernel.Sporadic.Fi24FiveK.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24FiveK.letc CFSG.KD.Fi24FiveK.Ck.l 0 17

namespace CFSG.KD.Fi24FiveK.Ck

theorem head : CFSG.KD.Fi24FiveK.head = true := by quickRfl

end CFSG.KD.Fi24FiveK.Ck

end
