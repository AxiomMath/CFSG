module

public import Certificates.Kernel.Sporadic.Fi24TwinK.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24TwinK.tbB CFSG.KD.Fi24TwinK.Ck.tbB 0 8

namespace CFSG.KD.Fi24TwinK.Ck

theorem fs1 : CFSG.KD.Fi24TwinK.fs 1 = true := by quickRfl
theorem pp1 : CFSG.KD.Fi24TwinK.pp 1 = true := by quickRfl
theorem cv1 : CFSG.KD.Fi24TwinK.cv 1 = true := by quickRfl
theorem ro1 : CFSG.KD.Fi24TwinK.ro 1 = true := by quickRfl
theorem k21 : CFSG.KD.Fi24TwinK.k2 1 = true := by quickRfl
theorem nm1 : CFSG.KD.Fi24TwinK.nm 1 = true := by quickRfl
theorem c21 : CFSG.KD.Fi24TwinK.c2 1 = true := by quickRfl
theorem cj1 : CFSG.KD.Fi24TwinK.cj 1 = true := by quickRfl

end CFSG.KD.Fi24TwinK.Ck

end
