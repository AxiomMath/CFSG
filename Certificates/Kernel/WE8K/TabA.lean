module

public import Certificates.Kernel.WE8K.TData
import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000

public section

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K

theorem ch18004_rt : rtOK rT adjM = true := by decide +kernel

theorem ch18004_adj : Nat.beq adjM adjC = true := by decide +kernel

theorem ch18004_tabN : tabNOK rT negP = true := by decide +kernel

#kc_slice_range CFSG.KD.WE8K.tabPFam ch18004P 0 8

#kc_slice_range CFSG.KD.WE8K.tabDFam ch18004D 0 8

#kc_slice_range CFSG.KD.WE8K.startFam ch18004s 0 10

#kc_slice_range CFSG.KD.WE8K.zwFam ch18004z 0 3

end CFSG.KD.WE8K

end
