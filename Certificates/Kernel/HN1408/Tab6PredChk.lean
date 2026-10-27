module

public import Certificates.Kernel.HN1408.Tab6PredDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408 CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ch441694_ne0 :
    (!Nat.beq (pt (WK (tab6Row0.conj ++ wordAZ ++ tab6Row0.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne1 :
    (!Nat.beq (pt (WK (tab6Row1.conj ++ wordAZ ++ tab6Row1.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne2 :
    (!Nat.beq (pt (WK (tab6Row2.conj ++ wordAZ ++ tab6Row2.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne3 :
    (!Nat.beq (pt (WK (tab6Row3.conj ++ wordAZ ++ tab6Row3.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne4 :
    (!Nat.beq (pt (WK (tab6Row4.conj ++ wordAZ ++ tab6Row4.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne5 :
    (!Nat.beq (pt (WK (tab6Row5.conj ++ wordAZ ++ tab6Row5.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne6 :
    (!Nat.beq (pt (WK (tab6Row6.conj ++ wordAZ ++ tab6Row6.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_ne7 :
    (!Nat.beq (pt (WK (tab6Row7.conj ++ wordAZ ++ tab6Row7.conj.reverse)) 0) (pt (WK wordAZ) 0)) =
      true := by quickRfl

theorem ch441694_p0 : conjK tab6W0 (WK wordAZ) (xK tab6Row0.conj) = true := by quickRfl

theorem ch441694_p1 : conjK tab6W1 (WK wordZ) (xK tab6Row1.conj) = true := by quickRfl

theorem ch441694_p2e : Nat.beq (powK (xK tab6Row2.conj) 3) idK = true := by quickRfl

theorem ch441694_p2m : movesK (xK tab6Row2.conj) = true := by quickRfl

theorem ch441694_p3e : Nat.beq (powK (xK tab6Row3.conj) 4) idK = true := by quickRfl

theorem ch441694_p3m : movesK (powK (xK tab6Row3.conj) 2) = true := by quickRfl

theorem ch441694_p3c : conjK tab6W3 (WK wordZ) (powK (xK tab6Row3.conj) 2) = true := by quickRfl

theorem ch441694_p4e : Nat.beq (powK (xK tab6Row4.conj) 4) idK = true := by quickRfl

theorem ch441694_p4m : movesK (powK (xK tab6Row4.conj) 2) = true := by quickRfl

theorem ch441694_p4c : conjK tab6W4 (WK wordAZ) (powK (xK tab6Row4.conj) 2) = true := by quickRfl

theorem ch441694_p5e : Nat.beq (powK (xK tab6Row5.conj) 5) idK = true := by quickRfl

theorem ch441694_p5m : movesK (xK tab6Row5.conj) = true := by quickRfl

theorem ch441694_p5c : conjK tab6W5 (WK fix5C.rep) (xK tab6Row5.conj) = true := by quickRfl

theorem ch441694_p6e : Nat.beq (powK (xK tab6Row6.conj) 5) idK = true := by quickRfl

theorem ch441694_p6m : movesK (xK tab6Row6.conj) = true := by quickRfl

theorem ch441694_p6c : conjK tab6W6 (WK fix5B.rep) (xK tab6Row6.conj) = true := by quickRfl

theorem ch441694_p7e : Nat.beq (powK (xK tab6Row7.conj) 6) idK = true := by quickRfl

theorem ch441694_p7m2 : movesK (powK (xK tab6Row7.conj) 2) = true := by quickRfl

theorem ch441694_p7m3 : movesK (powK (xK tab6Row7.conj) 3) = true := by quickRfl

theorem ch441694_p7c : conjK tab6W7 (WK wordAZ) (powK (xK tab6Row7.conj) 3) = true := by quickRfl

end CFSG.KD.HN1408.Tab6

end
