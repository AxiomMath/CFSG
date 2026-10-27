module

public import Certificates.Kernel.Sporadic.Fi24F4.JC
import CFSG.Certificates.Kernel.Common.SliceRange
public import Mathlib.Data.Matrix.Mul

public section

#kc_slice_range CFSG.KD.Fi24F4.sxc CFSG.KD.Fi24F4.Ck.sxc 0 5
#kc_slice_range CFSG.KD.Fi24F4.cubec CFSG.KD.Fi24F4.Ck.cubec 0 5
#kc_slice_range CFSG.KD.Fi24F4.commc CFSG.KD.Fi24F4.Ck.commc 0 25
#kc_slice_range CFSG.KD.Fi24F4.snc CFSG.KD.Fi24F4.Ck.snc 0 2
#kc_slice_range CFSG.KD.Fi24F4.relc CFSG.KD.Fi24F4.Ck.relc 0 10
#kc_slice_range CFSG.KD.Fi24F4.sqc CFSG.KD.Fi24F4.Ck.sqc 0 13

namespace CFSG.KD.Fi24F4.Ck

theorem fix : CFSG.KD.Fi24F4.fixc = true := by quickRfl

theorem qne : CFSG.KD.Fi24F4.qnec = true := by quickRfl

end CFSG.KD.Fi24F4.Ck

end
