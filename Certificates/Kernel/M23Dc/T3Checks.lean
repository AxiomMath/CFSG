module

public import Certificates.Kernel.M23Dc.Defs
public import Certificates.Data.M23T3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc

theorem t3nnB : ((List.range' 10 5).all fun j => (oc j).1.flatten.any fun l =>
    sT.any fun s => !(codeSetT 23 s l == l)) = true := by quickRfl

theorem t3e9 : M23T3.e9 := by decide +kernel

end CFSG.KD.M23Dc

end
