module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

#kc_slice_range CFSG.KD.Fi24P7.ok3 CFSG.KD.Fi24P7.S3.c 0 75

namespace CFSG.KD.Fi24P7

#kc_forall_tree S3.all (fun c => ok3 c = true) 75 CFSG.KD.Fi24P7.S3.c

end CFSG.KD.Fi24P7

end
