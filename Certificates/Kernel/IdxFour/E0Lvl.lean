module

public import Certificates.Kernel.IdxFour.E0Data
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4E cf17601lv (fun i => CFSG.KD.IF4E.lvl i) 0 5

namespace CFSG.KD.IF4E

theorem cf17601gens : gens = true := by decide +kernel

end CFSG.KD.IF4E

end
