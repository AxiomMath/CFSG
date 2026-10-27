module

public import Certificates.Kernel.Misc.G23F3Roots
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsG2Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G23F3

open CFSG.KC.Ord CFSG.KC.Misc.G23F3 CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift

theorem lift_ok : andB constsK (liftK RK (eqPairs.map fun p => (p.1.map Fin.val, p.2.map Fin.val))
    (nePairs.map (List.map Fin.val))) = true := by
  quickRfl

end CFSG.KD.Misc.G23F3

end
