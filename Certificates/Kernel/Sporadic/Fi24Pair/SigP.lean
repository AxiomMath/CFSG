module

public import Certificates.Kernel.Sporadic.Fi24Pair.DataP
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

#kc_slice_range CFSG.KD.Fi24Pair.sgp CFSG.KD.Fi24Pair.CkP.s 0 18

namespace CFSG.KD.Fi24Pair.CkP

#kc_forall_tree sgp_all (fun k => CFSG.KD.Fi24Pair.sgp k = true) 18 CFSG.KD.Fi24Pair.CkP.s

theorem cfc_t : CFSG.KD.Fi24Pair.cfc = true := by quickRfl

end CFSG.KD.Fi24Pair.CkP

end
