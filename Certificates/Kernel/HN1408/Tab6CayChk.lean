module

public import Certificates.Kernel.HN1408.Tab6CayData
public import Certificates.Kernel.HN1408.Tab6CayDefs
public import Certificates.Kernel.HN1408.CayleyDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441694_h2 : cyHd (tab6Row2.stabWords classaz.centGens) 48 tab6Cap Tab6S2.G Tab6S2.GI
    Tab6S2I Tab6S2.T Tab6S2.PL Tab6S2.cnt = true := by quickRfl
theorem ch441694_h4 : cyHd (tab6Row4.stabWords classaz.centGens) 32 tab6Cap Tab6S4.G Tab6S4.GI
    Tab6S4I Tab6S4.T Tab6S4.PL Tab6S4.cnt = true := by quickRfl
theorem ch441694_h6 : cyHd (tab6Row6.stabWords classaz.centGens) 20 tab6Cap Tab6S6.G Tab6S6.GI
    Tab6S6I Tab6S6.T Tab6S6.PL Tab6S6.cnt = true := by quickRfl
theorem ch441694_h7 : cyHd (tab6Row7.stabWords classaz.centGens) 16 tab6Cap Tab6S7.G Tab6S7.GI
    Tab6S7I Tab6S7.T Tab6S7.PL Tab6S7.cnt = true := by quickRfl

theorem ch441694_r2 : cyRec (tab6Row2.stabWords classaz.centGens).length Tab6S2.G Tab6S2.GI Tab6S2I
    Tab6S2.T Tab6S2.PL Tab6S2.POS Tab6S2.SRT Tab6S2.SRI Tab6S2.HS Tab6S2.HSI Tab6S2Cl Tab6S2.cnt =
    true := by quickRfl
theorem ch441694_r4 : cyRec (tab6Row4.stabWords classaz.centGens).length Tab6S4.G Tab6S4.GI Tab6S4I
    Tab6S4.T Tab6S4.PL Tab6S4.POS Tab6S4.SRT Tab6S4.SRI Tab6S4.HS Tab6S4.HSI Tab6S4Cl Tab6S4.cnt =
    true := by quickRfl
theorem ch441694_r6 : cyRec (tab6Row6.stabWords classaz.centGens).length Tab6S6.G Tab6S6.GI Tab6S6I
    Tab6S6.T Tab6S6.PL Tab6S6.POS Tab6S6.SRT Tab6S6.SRI Tab6S6.HS Tab6S6.HSI Tab6S6Cl Tab6S6.cnt =
    true := by quickRfl
theorem ch441694_r7 : cyRec (tab6Row7.stabWords classaz.centGens).length Tab6S7.G Tab6S7.GI Tab6S7I
    Tab6S7.T Tab6S7.PL Tab6S7.POS Tab6S7.SRT Tab6S7.SRI Tab6S7.HS Tab6S7.HSI Tab6S7Cl Tab6S7.cnt =
    true := by quickRfl

theorem ch441694_c2 : cayK t6Mul2 24 [47, 22, 40] (tab6Row2.stabWords classaz.centGens).length
    Tab6S2.cnt Tab6S2.PL Tab6S2Cl (cayCodes t6Mul2 24 [47, 22, 40] Tab6S2.PL Tab6S2.cnt) = true := by
  quickRfl
theorem ch441694_c4 : cayK t6Mul4 0 [10, 1, 20, 15] (tab6Row4.stabWords classaz.centGens).length
    Tab6S4.cnt Tab6S4.PL Tab6S4Cl (cayCodes t6Mul4 0 [10, 1, 20, 15] Tab6S4.PL Tab6S4.cnt) =
    true := by quickRfl
theorem ch441694_c6 : cayK t6Mul6 0 [19, 2, 18] (tab6Row6.stabWords classaz.centGens).length
    Tab6S6.cnt Tab6S6.PL Tab6S6Cl (cayCodes t6Mul6 0 [19, 2, 18] Tab6S6.PL Tab6S6.cnt) = true := by
  quickRfl
theorem ch441694_c7 : cayK t6Mul7 0 [6, 9, 1] (tab6Row7.stabWords classaz.centGens).length
    Tab6S7.cnt Tab6S7.PL Tab6S7Cl (cayCodes t6Mul7 0 [6, 9, 1] Tab6S7.PL Tab6S7.cnt) = true := by
  quickRfl

end CFSG.KD.HN1408.Tab6

end
