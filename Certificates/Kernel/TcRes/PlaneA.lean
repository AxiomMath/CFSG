module

public import Certificates.Kernel.TcRes.PlaneData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.TcRes.ch715750p tab CFSG.KD.TcRes.C1P.tab 0 9
#kc_each CFSG.KD.TcRes.ch715750p rc CFSG.KD.TcRes.C1P.rc 0 72
#kc_each CFSG.KD.TcRes.ch715750p pw CFSG.KD.TcRes.C1P.pw 0 25
#kc_each CFSG.KD.TcRes.ch715750p sw CFSG.KD.TcRes.C1P.sw 0 70
#kc_each CFSG.KD.TcRes.ch715750p sw CFSG.KD.TcRes.C1P.sw 72 75

end
