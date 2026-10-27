module

public import Certificates.Kernel.Sporadic.Fi24FreeK.Data
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24FreeK.cj CFSG.KD.Fi24FreeK.Ck.cj 0 6
#kc_slice_range CFSG.KD.Fi24FreeK.rel CFSG.KD.Fi24FreeK.Ck.rel 0 26
#kc_slice_range CFSG.KD.Fi24FreeK.stk CFSG.KD.Fi24FreeK.Ck.stk 0 12
#kc_slice_range CFSG.KD.Fi24FreeK.lmk CFSG.KD.Fi24FreeK.Ck.lmk 0 6

namespace CFSG.KD.Fi24FreeK.Ck

theorem pts_t : CFSG.KD.Fi24FreeK.pts = true := by quickRfl
theorem frm_t : CFSG.KD.Fi24FreeK.frm = true := by quickRfl
theorem ef_t : CFSG.KD.Fi24FreeK.ef = true := by quickRfl
theorem e0m_t : CFSG.KD.Fi24FreeK.e0m = true := by quickRfl
theorem ghk_t : CFSG.KD.Fi24FreeK.ghk = true := by quickRfl
theorem ppc_t : CFSG.KD.Fi24FreeK.ppc = true := by quickRfl
theorem lmp_t : CFSG.KD.Fi24FreeK.lmp = true := by quickRfl

end CFSG.KD.Fi24FreeK.Ck

end
