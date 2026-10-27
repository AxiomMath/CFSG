module

public import Certificates.Kernel.Sporadic.Fi24Pump.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24Pump.pck CFSG.KD.Fi24Pump.Ck.p 0 4

end
