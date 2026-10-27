module

public import Certificates.Kernel.RuIdx2.DefsX
import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

#kss_each CFSG.KD.RuIdx2.X CFSG.KD.RuIdx2.famX 7

namespace CFSG.KD.RuIdx2

theorem topW : famT = true := by quickRfl

end CFSG.KD.RuIdx2

end
