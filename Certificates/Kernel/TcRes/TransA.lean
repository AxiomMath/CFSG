module

public import Certificates.Kernel.TcRes.TransData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.TcRes.ch715751t

theorem bt : E8T.bt = true := by quickRfl

theorem root : E8T.nd0 = true := by quickRfl

end CFSG.KD.TcRes.ch715751t

#kc_each CFSG.KD.TcRes.ch715751t q CFSG.KD.TcRes.E8T.q 0 240
#kc_each CFSG.KD.TcRes.ch715751t mv CFSG.KD.TcRes.E8T.mv 0 240
#kc_each CFSG.KD.TcRes.ch715751t nd CFSG.KD.TcRes.E8T.nd 0 550

end
