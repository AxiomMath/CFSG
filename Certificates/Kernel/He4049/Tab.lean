module

public import Certificates.Kernel.He4049.T
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Data.Kernel.HeOrbK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxHeartbeats 0

public section

namespace CFSG.KD.He4049.Tab

open CFSG.KC.HeOrb

theorem ta_ok : tabK CFSG.KD.HeOrb.AL 14 16383 (CFSG.KD.He4049.TF 0) = true := by quickRfl

theorem tb_ok : tabK CFSG.KD.HeOrb.BE 14 16383 (CFSG.KD.He4049.TF 1) = true := by quickRfl

theorem neg_ab : (!tabK CFSG.KD.HeOrb.AL 14 16383 (CFSG.KD.He4049.TF 1)) = true := by quickRfl

end CFSG.KD.He4049.Tab

end
