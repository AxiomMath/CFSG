module

public import Certificates.Kernel.Misc.RuCoverNet.Data7296
public import Certificates.Data.Kernel.Misc.RuCoverNet7296
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.LieType.Multipliers.CoverWords

public section

set_option maxRecDepth 100000

namespace CFSG.KD.RuCoverNet7296

open CFSG.KC CFSG.KC.YModel CFSG.KC.Misc.RuCoverNet CFSG.EvenSporadicStandard.TwoRu.CentCover

#kc_each CFSG.KD.RuCoverNet7296 ch7296n
  (fun c => neW V 11 21 0 (Bool.rec (motive := fun _ => List Int) (etaW 6 c) y5W (Nat.beq c 0)) []
    (NB c) (NX c) (NY c)) 0 64

#kc_each CFSG.KD.RuCoverNet7296 ch7296g
  (fun k => Bool.rec (motive := fun _ => Bool)
    (neW V 11 21 0 (cosU k (KI k)) (cosV k (KI k)) (KB k) (KX k) (KY k)) true
    (Nat.beq (k / 16) (k % 16))) 0 256

end CFSG.KD.RuCoverNet7296

end
