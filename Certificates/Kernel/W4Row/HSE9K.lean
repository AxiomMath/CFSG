module

public import Certificates.Data.Kernel.W4Row.EPackK
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.W4RowHSE9
public import Certificates.Kernel.LocalQT.SV.C4126T
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 400000

namespace CFSG.KD.W4E.HSE9

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.W4E CFSG.KC.IntLines CFSG.KC.LQT.Cov
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CFSG.KD.LQT.C4126

@[expose] def strsC : List (List Char) :=
  [hsE9WXStr.toList, hsE9WYStr.toList, hsE9WM1Str.toList, hsE9WM2Str.toList, hsE9WM3Str.toList,
   hsE9WKStr.toList, hsE9WH5Str.toList, hsE9WH12Str.toList, hsE9WH21Str.toList,
   hsE9WH34Str.toList]

theorem strs : (strsC.all fun l => (intsSK (tokK l)).isSome) = true := by
  unfold strsC
  str_lits hsE9WXStr
  str_lits hsE9WYStr
  str_lits hsE9WM1Str
  str_lits hsE9WM2Str
  str_lits hsE9WM3Str
  str_lits hsE9WKStr
  str_lits hsE9WH5Str
  str_lits hsE9WH12Str
  str_lits hsE9WH21Str
  str_lits hsE9WH34Str
  simp only [String.toList_ofList]
  quickRfl

theorem pack : e9FullK 3850 12 [HS.F 0, HS.F 1] [HSI 0, HSI 1] [HC.F 5, HC.F 12, HC.F 21, HC.F 34]
    (lineInts hsE9WXStr.toList) (lineInts hsE9WYStr.toList) (lineInts hsE9WM1Str.toList)
    (lineInts hsE9WM2Str.toList) (lineInts hsE9WM3Str.toList) (lineInts hsE9WKStr.toList)
    [lineInts hsE9WH5Str.toList, lineInts hsE9WH12Str.toList, lineInts hsE9WH21Str.toList,
     lineInts hsE9WH34Str.toList] = true := by
  str_lits hsE9WXStr
  str_lits hsE9WYStr
  str_lits hsE9WM1Str
  str_lits hsE9WM2Str
  str_lits hsE9WM3Str
  str_lits hsE9WKStr
  str_lits hsE9WH5Str
  str_lits hsE9WH12Str
  str_lits hsE9WH21Str
  str_lits hsE9WH34Str
  simp only [String.toList_ofList]
  quickRfl

end CFSG.KD.W4E.HSE9

end
