module

public import Certificates.Kernel.HN1408.Tab6CayData
public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab65ACheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408 CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441694_k2 : allN (tab6Row2.stabWords classaz.centGens).length (fun j =>
    bAnd(commP (Tab6S2.GI j) (WK wordAZ),
      commP (Tab6S2.GI j) (WK (tab6Row2.conj ++ wordAZ ++ tab6Row2.conj.reverse)))) = true := by
  quickRfl

theorem ch441694_k4 : allN (tab6Row4.stabWords classaz.centGens).length (fun j =>
    bAnd(commP (Tab6S4.GI j) (WK wordAZ),
      commP (Tab6S4.GI j) (WK (tab6Row4.conj ++ wordAZ ++ tab6Row4.conj.reverse)))) = true := by
  quickRfl

theorem ch441694_k6 : allN (tab6Row6.stabWords classaz.centGens).length (fun j =>
    bAnd(commP (Tab6S6.GI j) (WK wordAZ),
      commP (Tab6S6.GI j) (WK (tab6Row6.conj ++ wordAZ ++ tab6Row6.conj.reverse)))) = true := by
  quickRfl

theorem ch441694_k7 : allN (tab6Row7.stabWords classaz.centGens).length (fun j =>
    bAnd(commP (Tab6S7.GI j) (WK wordAZ),
      commP (Tab6S7.GI j) (WK (tab6Row7.conj ++ wordAZ ++ tab6Row7.conj.reverse)))) = true := by
  quickRfl

theorem ch441694_k5y : commP (WK tab65AWord) (WK wordAZ) = true := by quickRfl

theorem ch441694_k5c :
    commP (WK tab65AWord) (WK (tab6Row5.conj ++ wordAZ ++ tab6Row5.conj.reverse)) = true := by
  quickRfl

end CFSG.KD.HN1408.Tab6

end
