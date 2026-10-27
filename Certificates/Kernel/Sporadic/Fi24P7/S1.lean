module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

#kc_slice_range CFSG.KD.Fi24P7.ok1 CFSG.KD.Fi24P7.S1.c 0 75

namespace CFSG.KD.Fi24P7

#kc_forall_tree S1.all (fun c => ok1 c = true) 75 CFSG.KD.Fi24P7.S1.c

end CFSG.KD.Fi24P7

end
