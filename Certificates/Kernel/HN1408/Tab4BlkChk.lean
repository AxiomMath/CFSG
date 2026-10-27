module

public import Certificates.Kernel.HN1408.Tab4BlkDefs
public import Certificates.Kernel.HN1408.Tab4BlkData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import Certificates.Kernel.HN1408.CzTDefs
public import Certificates.Kernel.HN1408.Tab4CntDefs
public import Certificates.Kernel.HN1408.TabXCntDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbT

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.Tab4Blk
open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441693_tB2 : tabK LB2 DB2 PB2 RB2 12 6 = true := by quickRfl

theorem ch441693_tS2 : tabK LS2 DS2 PS2 RS2 4 2 = true := by quickRfl

theorem ch441693_tB4 : tabK LB4 DB4 PB4 RB4 120 5 = true := by quickRfl

theorem ch441693_tS4 : tabK LS4 DS4 PS4 RS4 4 2 = true := by quickRfl

theorem ch441693_tB5 : tabK LB5 DB5 PB5 RB5 240 5 = true := by quickRfl

theorem ch441693_tS5 : tabK LS5 DS5 PS5 RS5 4 2 = true := by quickRfl

theorem ch441693_b2 : shapeK (WK (tab4Row2.conj ++ wordB ++ tab4Row2.conj.reverse))
    LB2 DB2 RB2 12 LS2 DS2 RS2 4 = true := by quickRfl

theorem ch441693_b4 : shapeK (WK (tab4Row4.conj ++ wordB ++ tab4Row4.conj.reverse))
    LB4 DB4 RB4 120 LS4 DS4 RS4 4 = true := by quickRfl

theorem ch441693_b5 : shapeK (WK (tab4Row5.conj ++ wordB ++ tab4Row5.conj.reverse))
    LB5 DB5 RB5 240 LS5 DS5 RS5 4 = true := by quickRfl

theorem ch441693_k2 : kerK (WK (tab4Row2.conj ++ wordB ++ tab4Row2.conj.reverse))
    LB2 RB2 6 LS2 RS2 = true := by quickRfl

theorem ch441693_k4 : kerK (WK (tab4Row4.conj ++ wordB ++ tab4Row4.conj.reverse))
    LB4 RB4 5 LS4 RS4 = true := by quickRfl

theorem ch441693_k5 : kerK (WK (tab4Row5.conj ++ wordB ++ tab4Row5.conj.reverse))
    LB5 RB5 5 LS5 RS5 = true := by quickRfl

end CFSG.KD.HN1408.CbT

end
