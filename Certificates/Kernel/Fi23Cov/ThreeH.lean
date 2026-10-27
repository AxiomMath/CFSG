module

public import Certificates.Kernel.Fi23Cov.Three
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false
public section

#kc_slice_range CFSG.KD.Fi23Cov.rep CFSG.KD.Fi23Cov.Ck.r 0 4
#kc_slice_range CFSG.KD.Fi23Cov.cL CFSG.KD.Fi23Cov.Ck.cL 0 8
#kc_slice_range CFSG.KD.Fi23Cov.dL CFSG.KD.Fi23Cov.Ck.dL 0 8

namespace CFSG.KD.Fi23Cov.Ck

theorem gens : CFSG.KD.Fi23Cov.gens = true := by quickRfl

theorem ctl0 : CFSG.KD.Fi23Cov.ctl0 = true := by quickRfl

theorem ctl1 : CFSG.KD.Fi23Cov.ctl1 = true := by quickRfl

theorem cH : CFSG.KD.Fi23Cov.cH = true := by quickRfl

theorem cP : CFSG.KD.Fi23Cov.cP = true := by quickRfl

theorem dH : CFSG.KD.Fi23Cov.dH = true := by quickRfl

theorem dP : CFSG.KD.Fi23Cov.dP = true := by quickRfl

end CFSG.KD.Fi23Cov.Ck

end
