module

public import Certificates.Kernel.Fi23Cov.Five
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false
public section

#kc_slice_range CFSG.KD.Fi23Cov.letc CFSG.KD.Fi23Cov.Ck.l 0 14

namespace CFSG.KD.Fi23Cov.Ck

theorem head : CFSG.KD.Fi23Cov.head = true := by quickRfl

theorem pa : CFSG.KD.Fi23Cov.prA = true := by quickRfl

theorem pb : CFSG.KD.Fi23Cov.prB = true := by quickRfl

end CFSG.KD.Fi23Cov.Ck

end
