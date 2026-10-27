module

public import Certificates.Kernel.TwoHS.HYWords
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS

theorem winv_ok :
    (Nat.beq (pcomp 11200 14 (mask 14) (UK [1]) (UK [1])) idK && !Nat.beq (UK [1]) idK &&
      Nat.beq (pcomp 11200 14 (mask 14) (UK [2, 3, 3]) (UK [2, 3, 3])) idK &&
      !Nat.beq (UK [2, 3, 3]) idK) = true := by
  quickRfl

end CFSG.KD.TwoHS

end
