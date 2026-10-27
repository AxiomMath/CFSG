module

public import Certificates.Kernel.TcRes.ForestData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_each CFSG.KD.TcRes.ch715750c1 rep CFSG.KD.TcRes.C1.rep 0 25
#kc_each CFSG.KD.TcRes.ch715750c1 leaf CFSG.KD.TcRes.C1.leaf 0 405

end
