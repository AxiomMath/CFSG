module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Split
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24ThreeO.ct CFSG.KD.Fi24ThreeO.Ck.ct 0 26
#kc_slice_range CFSG.KD.Fi24ThreeO.cst CFSG.KD.Fi24ThreeO.Ck.cst 0 3
#kc_slice_range CFSG.KD.Fi24ThreeO.bs CFSG.KD.Fi24ThreeO.Ck.bs 0 6

#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.BG (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) (CFSG.KD.Fi24ThreeO.uC CFSG.KD.Fi24ThreeO.bk ++ CFSG.KD.Fi24ThreeO.uC CFSG.KD.Fi24ThreeO.bl) 4

namespace CFSG.KD.Fi24ThreeO.Ck

theorem bg_t : CFSG.KD.Fi24ThreeO.bg = true := by
  unfold CFSG.KD.Fi24ThreeO.bg
  rw [CFSG.KD.Fi24Kit.Split.offOK_eq, CFSG.KD.Fi24Kit.Split.offS_eq, BG.eq]
  quickRfl

end CFSG.KD.Fi24ThreeO.Ck

end
