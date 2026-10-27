module

public import Certificates.Kernel.HN1408.M11DefsR
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Defs
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

#kc_each CFSG.KD.HN1408.hvR 8 16
#kc_each CFSG.KD.HN1408.hsR 0 2

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnumR

theorem m11hvF_neg : (!hvF 1408 11 (mask 11) MR1.T (fun i => Nat.succ (MR1V i)) 5) = true := by
  quickRfl

theorem m11peR_neg : (!penumPtR 1408 11 (mask 11) MR1.GI 2 MR1.cnt MR1.T MR1.PL (fun _ => 0)
    MR1.SRT MR1.SRI 5) = true := by
  quickRfl

end CFSG.KD.HN1408

end
