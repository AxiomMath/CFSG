module

public import Certificates.Kernel.LocalQT.Small.C4066
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.LQT.C4066.Neg

open CFSG.KC.Ord CFSG.KC.LQT.A6 CFSG.QuasithinUnique.Id2519.UHS

theorem swap : notB (a6K A0 A1 A1i y2Letters y1Letters cLetters nodePar.toList nodeLab.toList
    conjWords.toList) = true := by quickRfl

theorem par : notB (a6K A0 A1 A1i y1Letters y2Letters cLetters nodePar.toList.dropLast
    nodeLab.toList conjWords.toList) = true := by quickRfl

theorem canon : notB (a6K (A0 + 2 ^ 46200) A1 A1i y1Letters y2Letters cLetters nodePar.toList
    nodeLab.toList conjWords.toList) = true := by quickRfl

end CFSG.KD.LQT.C4066.Neg

end
