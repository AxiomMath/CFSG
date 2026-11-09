module

public import Certificates.Kernel.Sporadic.Fi24FiveK.DataT
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi24FiveK.SliceEq

set_option Elab.async false

public section

#kc_slice_range_eq CFSG.KD.Fi24FiveK.blk CFSG.KD.Fi24FiveK.Ck.q CFSG.KD.Fi24FiveK.blk_eq 0 11

namespace CFSG.KD.Fi24FiveK.Ck

theorem p : CFSG.KD.Fi24FiveK.prd = true := by quickRfl

end CFSG.KD.Fi24FiveK.Ck

end
