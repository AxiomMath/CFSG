module

public import Certificates.Kernel.Sporadic.Fi24P7.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

#kc_slice_range CFSG.KD.Fi24P7.ck0 CFSG.KD.Fi24P7.O0.c 0 4
#kc_slice_range CFSG.KD.Fi24P7.cq2 CFSG.KD.Fi24P7.Q2.c 0 6
#kc_slice_range CFSG.KD.Fi24P7.cq4 CFSG.KD.Fi24P7.Q4.c 0 44

namespace CFSG.KD.Fi24P7

open CFSG.KC.Loop

#kc_forall_tree O0.all (fun c => ck0 c = true) 4 CFSG.KD.Fi24P7.O0.c
#kc_forall_tree Q2.all (fun c => cq2 c = true) 6 CFSG.KD.Fi24P7.Q2.c
#kc_forall_tree Q4.all (fun c => cq4 c = true) 44 CFSG.KD.Fi24P7.Q4.c

theorem P2.all : allBelow 378 6 pt2 = true := by quickRfl

theorem P4.all : allBelow 351 6 pt4 = true := by quickRfl

end CFSG.KD.Fi24P7

end
