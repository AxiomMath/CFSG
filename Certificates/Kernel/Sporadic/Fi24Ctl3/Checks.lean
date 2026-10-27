module

public import Certificates.Kernel.Sporadic.Fi24Ctl3.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24Ctl3.ck CFSG.KD.Fi24Ctl3.Ck.c 0 5

end
