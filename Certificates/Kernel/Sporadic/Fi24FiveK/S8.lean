module

public import Certificates.Kernel.Sporadic.Fi24FiveK.DataT
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi24FiveK.SliceEq

set_option Elab.async false

public section

#kc_slice_range_eq CFSG.KD.Fi24FiveK.stg CFSG.KD.Fi24FiveK.Ck.s CFSG.KD.Fi24FiveK.stg_eq 224 252

end
