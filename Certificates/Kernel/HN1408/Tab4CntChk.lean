module

public import Certificates.Kernel.HN1408.Tab4CntDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import Certificates.Kernel.HN1408.CzTDefs
public import Certificates.Kernel.HN1408.TabXCntDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbT

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441693_s0 : stab2K (WK (tab4Row0.conj ++ wordB ++ tab4Row0.conj.reverse)) 768 = true := by
  quickRfl

theorem ch441693_s1 : stab2K (WK (tab4Row1.conj ++ wordB ++ tab4Row1.conj.reverse)) 768 = true := by
  quickRfl

theorem ch441693_s2 : stab2K (WK (tab4Row2.conj ++ wordB ++ tab4Row2.conj.reverse)) 1440 = true := by
  quickRfl

theorem ch441693_s3 : stab2K (WK (tab4Row3.conj ++ wordB ++ tab4Row3.conj.reverse)) 64 = true := by
  quickRfl

theorem ch441693_s4 : stab2K (WK (tab4Row4.conj ++ wordB ++ tab4Row4.conj.reverse)) 240 = true := by
  quickRfl

theorem ch441693_s5 : stab2K (WK (tab4Row5.conj ++ wordB ++ tab4Row5.conj.reverse)) 240 = true := by
  quickRfl

end CFSG.KD.HN1408.CbT

end
