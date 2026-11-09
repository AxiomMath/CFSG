module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Split
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24ThreeO.hc CFSG.KD.Fi24ThreeO.Ck.hc 0 6

#kn_iter CFSG.KD.Fi24ThreeO.Ck.HC (CFSG.KC.Fi24ThreeO.stepW CFSG.KD.Fi24Net.NW CFSG.KD.Fi24Kit.NT CFSG.KD.Fi24ThreeO.hw)
  (CFSG.KD.Fi24ThreeO.gfr (CFSG.KC.Fi24ThreeO.plOf CFSG.KD.Fi24ThreeO.hr)) (CFSG.KD.Fi24ThreeO.hd) 12 2

namespace CFSG.KD.Fi24ThreeO.Ck

theorem hcov_t : CFSG.KD.Fi24ThreeO.hcov = true := CFSG.KD.Fi24Kit.Split.covW_of HC.eq (by quickRfl)
theorem hq_t : CFSG.KD.Fi24ThreeO.hq = true := by quickRfl
theorem lks_t : CFSG.KD.Fi24ThreeO.lks = true := by quickRfl
theorem qcl_t : CFSG.KD.Fi24ThreeO.qcl = true := by quickRfl
theorem cuF_t : CFSG.KD.Fi24ThreeO.cuF = true := by quickRfl
theorem fpf_t : CFSG.KD.Fi24ThreeO.fpf = true := by quickRfl

end CFSG.KD.Fi24ThreeO.Ck

end
