module

public import Certificates.Kernel.Sporadic.Fi24Pc.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

public section

set_option maxRecDepth 200000

#kc_slice_range CFSG.KD.Fi24Pc.rck CFSG.KD.Fi24Pc.Ck.r 0 16
#kc_slice_range CFSG.KD.Fi24Pc.tck CFSG.KD.Fi24Pc.Ck.t 0 16
#kc_slice_range CFSG.KD.Fi24Pc.bck CFSG.KD.Fi24Pc.Ck.b 0 7
#kc_slice_range CFSG.KD.Fi24Pc.kck CFSG.KD.Fi24Pc.Ck.k 0 16

theorem CFSG.KD.Fi24Pc.Ck.l : CFSG.KD.Fi24Pc.lck = true := by quickRfl

end
