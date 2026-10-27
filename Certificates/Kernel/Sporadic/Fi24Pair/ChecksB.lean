module

public import Certificates.Kernel.Sporadic.Fi24Pair.Data
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_slice_range CFSG.KD.Fi24Pair.clo CFSG.KD.Fi24Pair.CkB.c 0 18
#kc_slice_range CFSG.KD.Fi24Pair.out CFSG.KD.Fi24Pair.CkB.o 0 6

namespace CFSG.KD.Fi24Pair.CkB

#kc_forall_tree clo_all (fun k => CFSG.KD.Fi24Pair.clo k = true) 18 CFSG.KD.Fi24Pair.CkB.c
#kc_forall_tree out_all (fun j => CFSG.KD.Fi24Pair.out j = true) 6 CFSG.KD.Fi24Pair.CkB.o

theorem pts_t : CFSG.KD.Fi24Pair.pts = true := by quickRfl
theorem reg_t : CFSG.KD.Fi24Pair.reg = true := by quickRfl
theorem orb0_t : CFSG.KD.Fi24Pair.orb0 = true := by quickRfl
theorem hw0_t : CFSG.KD.Fi24Pair.hw0 = true := by quickRfl
theorem hw1_t : CFSG.KD.Fi24Pair.hw1 = true := by quickRfl
theorem orb1_t : CFSG.KD.Fi24Pair.orb1 = true := by quickRfl

end CFSG.KD.Fi24Pair.CkB

end
