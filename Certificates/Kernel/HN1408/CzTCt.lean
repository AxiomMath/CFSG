module

public import Certificates.Kernel.HN1408.CzTScanDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzT

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem czT_ct : ctK T0 T1 (WK (tGens.getD 0 [])) (WK (tGens.getD 1 [])) (WK (tGens.getD 2 []))
    (WK wordA) (WK wordZ) = true := by
  quickRfl

end CFSG.KD.HN1408.CzT

end
