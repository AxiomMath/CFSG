module

public import Certificates.Kernel.WE8K.TData
import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000

public section

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K

theorem ch18004_qXP : qXOK false xp rT = true := by decide +kernel

theorem ch18004_qXM : qXOK true xm rT = true := by decide +kernel

#kc_slice_range CFSG.KD.WE8K.qPFam ch18004qp 0 8

#kc_slice_range CFSG.KD.WE8K.qMFam ch18004qm 0 8

end CFSG.KD.WE8K

end
