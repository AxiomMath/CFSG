module

public import Certificates.Kernel.J27031.T
public import Certificates.Data.Kernel.DcK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J27031

open CFSG.KC.DcK

theorem parse_ok : ((edgesK T.edges.chars).isSome && (natsK T.inEdge.chars).isSome &&
    (natsK T.dIn.chars).isSome && (natsK T.reach.chars).isSome &&
    (natsK T.outEdge.chars).isSome && (natsK T.dOut.chars).isSome) = true := by quickRfl

end CFSG.KD.J27031

end
