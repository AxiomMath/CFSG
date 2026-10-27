module

public import Certificates.Kernel.IdxFour.SaData
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.IF4S cf17607lv (fun i => CFSG.KD.IF4S.lvl i) 0 6

namespace CFSG.KD.IF4S

theorem cf17607gens : gens = true := by decide +kernel

end CFSG.KD.IF4S

end
