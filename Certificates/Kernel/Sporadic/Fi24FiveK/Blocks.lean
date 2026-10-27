module

public import Certificates.Kernel.Sporadic.Fi24FiveK.DataQ
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24FiveK.blk CFSG.KD.Fi24FiveK.Ck.q 0 11

namespace CFSG.KD.Fi24FiveK.Ck

theorem p : CFSG.KD.Fi24FiveK.prd = true := by quickRfl

end CFSG.KD.Fi24FiveK.Ck

end
