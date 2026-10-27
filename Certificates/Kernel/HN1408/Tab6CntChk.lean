module

public import Certificates.Kernel.HN1408.Tab6CntDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Data
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408.CzT CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441694_s0 : stab3K (WK (tab6Row0.conj ++ wordAZ ++ tab6Row0.conj.reverse)) 384 = true := by
  quickRfl

theorem ch441694_s1 : stab3K (WK (tab6Row1.conj ++ wordAZ ++ tab6Row1.conj.reverse)) 1024 = true := by
  quickRfl

theorem ch441694_s2 : stab3K (WK (tab6Row2.conj ++ wordAZ ++ tab6Row2.conj.reverse)) 48 = true := by
  quickRfl

theorem ch441694_s3 : stab3K (WK (tab6Row3.conj ++ wordAZ ++ tab6Row3.conj.reverse)) 64 = true := by
  quickRfl

theorem ch441694_s4 : stab3K (WK (tab6Row4.conj ++ wordAZ ++ tab6Row4.conj.reverse)) 32 = true := by
  quickRfl

theorem ch441694_s5 : stab3K (WK (tab6Row5.conj ++ wordAZ ++ tab6Row5.conj.reverse)) 240 = true := by
  quickRfl

theorem ch441694_s6 : stab3K (WK (tab6Row6.conj ++ wordAZ ++ tab6Row6.conj.reverse)) 20 = true := by
  quickRfl

theorem ch441694_s7 : stab3K (WK (tab6Row7.conj ++ wordAZ ++ tab6Row7.conj.reverse)) 16 = true := by
  quickRfl

end CFSG.KD.HN1408.Tab6

end
