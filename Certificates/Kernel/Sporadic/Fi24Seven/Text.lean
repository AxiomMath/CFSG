module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
public import Certificates.Kernel.Sporadic.Fi24Seven.Plan
public import Certificates.Data.Kernel.Spor.SlpText
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Data

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.HardMathSupport.Dickson.I271.Fi7 CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

theorem words7_txt : words7 = String.ofList (wordsC W7) := by
  str_lits words7
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem conj7_txt : conj7 = String.ofList (pairsC C7) := by
  str_lits conj7
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem fi7Extra_txt : fi7ExtraStr = String.ofList (wordsC E7) := by
  str_lits fi7ExtraStr
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem fi24kExtra_txt : fi24kExtraStr = String.ofList (wordsC EK) := by
  str_lits fi24kExtraStr
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

end CFSG.KD.F24S

end
