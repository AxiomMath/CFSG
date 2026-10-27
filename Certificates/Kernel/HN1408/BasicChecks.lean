module

public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.EvenSporadicStandard.HNRecog

theorem invol4 : bAnd(involK (WK wordA), bAnd(involK (WK wordZ), bAnd(involK (WK wordB),
    involK (WK wordZ₁)))) = true := by
  quickRfl

theorem centA : allN 7 (fun j => commP (WK wordA) (H8.F j)) = true := by
  quickRfl

theorem halvesA : halvesK (WK wordA) = true := by
  quickRfl

theorem halvesZ : halvesK (WK wordZ) = true := by
  quickRfl

theorem halvesAZ : halvesK (WK wordAZ) = true := by
  quickRfl

theorem swaps : bAnd(Nat.ble 704 (pt (WK wordB) 0), Nat.ble 704 (pt (WK wordZ₁) 0)) = true := by
  quickRfl

theorem gensInvo : allN 7 (fun j => Nat.beq (pc (WK [j + 1]) (WK [j + 1])) idK) = true := by
  quickRfl

theorem neg : bAnd(bIf(Nat.ble 704 (pt (WK wordZ) 0), false, true),
    bAnd(bIf(halvesK (WK wordB), false, true), bIf(halvesK (WK wordZ₁), false, true))) =
      true := by
  quickRfl

end CFSG.KD.HN1408

end
