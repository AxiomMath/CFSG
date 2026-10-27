module

public import Certificates.Kernel.Misc.RuCoverNet.Data7296
public import Certificates.Data.Kernel.Misc.RuCoverNet7296
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Recognition.RuMultiplierInputs
import CFSG.LieType.Multipliers.CoverWords

public section

set_option maxRecDepth 100000

namespace CFSG.KD.RuCoverNet7296

open CFSG.KC CFSG.KC.YModel CFSG.KC.Misc.RuCoverNet CFSG.EvenSporadicStandard.TwoRu.CentCover

#kc_each CFSG.KD.RuCoverNet7296 ch7296w (fun i => wordOK 14 6 2 V CP CL i) 0 20

theorem ch7296b0 : eqW V 11 21 0 (zW ++ zW) [] = true := by quickRfl

theorem ch7296b1 : eqW V 11 21 0 ([2] ++ zW) (zW ++ [2]) = true := by quickRfl

theorem ch7296b2 : eqW V 11 21 0 (y5W ++ y5W ++ y5W ++ y5W ++ y5W) [] = true := by quickRfl

#kc_each CFSG.KD.RuCoverNet7296 ch7296f (fun k => eqW V 11 21 0 (facW k) (jW k)) 0 6

#kc_each CFSG.KD.RuCoverNet7296 ch7296s (fun i => eqW V 11 21 0 (fW i ++ fW i) []) 0 6

#kc_each CFSG.KD.RuCoverNet7296 ch7296c
  (fun k => eqW V 11 21 0 (fW (k / 6) ++ fW (k % 6)) (fW (k % 6) ++ fW (k / 6))) 0 36

#kc_each CFSG.KD.RuCoverNet7296 ch7296m (fun k => eqW V 11 21 0 (memW k) (etaW 6 (MC k))) 0 80

#kc_each CFSG.KD.RuCoverNet7296 ch7296y (fun i => eqW V 11 21 0 (jW 4 ++ fW i) (fW i ++ jW 4)) 0 6

#kc_each CFSG.KD.RuCoverNet7296 ch7296x (fun i => eqW V 11 21 0 (y2W ++ fW i) (fW i ++ y2W)) 0 6

theorem ch7296z0 : eqW V 11 21 0 (commW (jW 4) y2W) zW = true := by quickRfl

end CFSG.KD.RuCoverNet7296

end
