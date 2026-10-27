module

public import Certificates.Kernel.TcRes.C2PlaneData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.TcRes.ch715751p

theorem pw : C2P.pw = true := by quickRfl

theorem k0 : C2P.k0 = true := by quickRfl

theorem k1 : C2P.k1 = true := by quickRfl

end CFSG.KD.TcRes.ch715751p

#kc_each CFSG.KD.TcRes.ch715751p tab CFSG.KD.TcRes.C2P.tab 0 5
#kc_each CFSG.KD.TcRes.ch715751p rc CFSG.KD.TcRes.C2P.rc 0 240
#kc_each CFSG.KD.TcRes.ch715751p sw CFSG.KD.TcRes.C2P.sw 0 2
#kc_each CFSG.KD.TcRes.ch715751p leaf CFSG.KD.TcRes.C2P.leaf 0 101

end
