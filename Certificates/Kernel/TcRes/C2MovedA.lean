module

public import Certificates.Kernel.TcRes.C2MovedData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.TcRes.ch715751m pos CFSG.KD.TcRes.C2M.pos 0 240
#kc_each CFSG.KD.TcRes.ch715751m dec CFSG.KD.TcRes.C2M.dec 0 240
#kc_each CFSG.KD.TcRes.ch715751m line CFSG.KD.TcRes.C2M.line 0 1038
#kc_each CFSG.KD.TcRes.ch715751m mleaf CFSG.KD.TcRes.C2M.leaf 0 101

end
