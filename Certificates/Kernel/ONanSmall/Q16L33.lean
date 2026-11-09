module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import Certificates.Kernel.ONanSmall.L33

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.Q16

open CFSG.CGT.PushingUpLit.SolKNA.R4.Check

theorem k9753 : (L33.repsA.zip L33.centsA).all (fun p => q16At p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.Q16

end
