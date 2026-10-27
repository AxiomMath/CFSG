module

public import Certificates.Kernel.TcRes.MovedData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.TcRes.ch715750m pos CFSG.KD.TcRes.C1M.pos 0 72
#kc_each CFSG.KD.TcRes.ch715750m dec CFSG.KD.TcRes.C1M.dec 0 72
#kc_each CFSG.KD.TcRes.ch715750m line CFSG.KD.TcRes.C1M.line 0 234
#kc_each CFSG.KD.TcRes.ch715750m mleaf CFSG.KD.TcRes.C1M.leaf 0 117

end
