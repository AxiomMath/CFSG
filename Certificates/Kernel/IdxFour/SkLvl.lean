module

public import Certificates.Kernel.IdxFour.SkData
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4K cf17612lv (fun i => CFSG.KD.IF4K.lvl i) 0 2

namespace CFSG.KD.IF4K

theorem cf17612gens : gens = true := by decide +kernel

end CFSG.KD.IF4K

end
