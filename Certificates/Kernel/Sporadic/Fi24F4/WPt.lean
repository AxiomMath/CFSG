module

public import Certificates.Kernel.Sporadic.Fi24F4.WC
import CFSG.Certificates.Kernel.Common.SliceRange

public section

set_option Elab.async false

#kc_slice_range CFSG.KD.Fi24F4.prd CFSG.KD.Fi24F4.Ck.prd 0 5
#kc_slice_range CFSG.KD.Fi24F4.wit CFSG.KD.Fi24F4.Ck.wit 0 5
#kc_slice_range CFSG.KD.Fi24F4.gph CFSG.KD.Fi24F4.Ck.gph 0 5
#kc_slice_range CFSG.KD.Fi24F4.fixq CFSG.KD.Fi24F4.Ck.fixq 0 5
#kc_slice_range CFSG.KD.Fi24F4.nd CFSG.KD.Fi24F4.Ck.nd 0 5

end
