module

public import Certificates.Data.Kernel.M24G.Trio12
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.Trio12Data

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.T12C

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem orb_ok : trioOrbF (piSteps T12D.PI) TL = true := by decide +kernel

end CFSG.KC.M24G.T12C
