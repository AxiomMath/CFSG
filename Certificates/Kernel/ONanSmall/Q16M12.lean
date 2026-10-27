module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import Certificates.Kernel.ONanSmall.M12A

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.Q16

open CFSG.CGT.PushingUpLit.SolKNA.R4.Check

theorem k9756 : (M12A.reps.zip M12A.cents).all (fun p => q16At p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.Q16

end
