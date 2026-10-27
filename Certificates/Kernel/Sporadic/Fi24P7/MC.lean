module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

#kc_slice_range CFSG.KD.Fi24P7.chA2 CFSG.KD.Fi24P7.CA2.c 0 10
#kc_slice_range CFSG.KD.Fi24P7.chA4 CFSG.KD.Fi24P7.CA4.c 0 11
#kc_slice_range CFSG.KD.Fi24P7.chB4 CFSG.KD.Fi24P7.CB4.c 0 11
#kc_slice_range CFSG.KD.Fi24P7.chS4 CFSG.KD.Fi24P7.CS4.c 0 5

namespace CFSG.KD.Fi24P7

#kc_forall_tree CA2.all (fun i => chA2 i = true) 10 CFSG.KD.Fi24P7.CA2.c
#kc_forall_tree CA4.all (fun i => chA4 i = true) 11 CFSG.KD.Fi24P7.CA4.c
#kc_forall_tree CB4.all (fun i => chB4 i = true) 11 CFSG.KD.Fi24P7.CB4.c
#kc_forall_tree CS4.all (fun i => chS4 i = true) 5 CFSG.KD.Fi24P7.CS4.c

end CFSG.KD.Fi24P7

end
