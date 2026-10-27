module

public import Certificates.Kernel.HN1408.Tab4PredDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import Certificates.Kernel.HN1408.Tab6PredDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab4

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408 CFSG.KD.HN1408.Tab6 CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441693_nb0 :
    ne01K (WK (tab4Row0.conj ++ wordB ++ tab4Row0.conj.reverse)) (WK wordB) = true := by quickRfl

theorem ch441693_nb1 :
    ne01K (WK (tab4Row1.conj ++ wordB ++ tab4Row1.conj.reverse)) (WK wordB) = true := by quickRfl

theorem ch441693_nb2 :
    ne01K (WK (tab4Row2.conj ++ wordB ++ tab4Row2.conj.reverse)) (WK wordB) = true := by quickRfl

theorem ch441693_nb3 :
    ne01K (WK (tab4Row3.conj ++ wordB ++ tab4Row3.conj.reverse)) (WK wordB) = true := by quickRfl

theorem ch441693_nb4 :
    ne01K (WK (tab4Row4.conj ++ wordB ++ tab4Row4.conj.reverse)) (WK wordB) = true := by quickRfl

theorem ch441693_nb5 :
    ne01K (WK (tab4Row5.conj ++ wordB ++ tab4Row5.conj.reverse)) (WK wordB) = true := by quickRfl

theorem ch441693_nab0 : ne01K (WK (tab4Row0.conj ++ wordB ++ tab4Row0.conj.reverse))
    (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_nab1 : ne01K (WK (tab4Row1.conj ++ wordB ++ tab4Row1.conj.reverse))
    (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_nab2 : ne01K (WK (tab4Row2.conj ++ wordB ++ tab4Row2.conj.reverse))
    (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_nab3 : ne01K (WK (tab4Row3.conj ++ wordB ++ tab4Row3.conj.reverse))
    (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_nab4 : ne01K (WK (tab4Row4.conj ++ wordB ++ tab4Row4.conj.reverse))
    (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_nab5 : ne01K (WK (tab4Row5.conj ++ wordB ++ tab4Row5.conj.reverse))
    (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_ab : conjK tab4Wab (WK wordB) (pc (WK wordA) (WK wordB)) = true := by quickRfl

theorem ch441693_p0 : conjK tab4W0 (WK wordAZ) (xB tab4Row0.conj) = true := by quickRfl

theorem ch441693_p1 : conjK tab4W1 (WK wordZ) (xB tab4Row1.conj) = true := by quickRfl

theorem ch441693_p2 : Nat.beq (powK (xB tab4Row2.conj) 2) (WK wordA) = true := by quickRfl

theorem ch441693_p3 : conjK tab4W3 (WK wordZ) (powK (xB tab4Row3.conj) 2) = true := by quickRfl

theorem ch441693_p4e : Nat.beq (powK (xB tab4Row4.conj) 3) idK = true := by quickRfl

theorem ch441693_p4m : movesK (xB tab4Row4.conj) = true := by quickRfl

theorem ch441693_p5 : Nat.beq (powK (xB tab4Row5.conj) 3) (WK wordA) = true := by quickRfl

end CFSG.KD.HN1408.Tab4

end
