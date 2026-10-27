module

public import Certificates.Data.Kernel.W4Row.WordLitK
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.W4RowHeE25
public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.W4Row.HeE25W
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.W4E.HeE25

open CFSG.KC.Enum CFSG.KS CFSG.KC.W4E CFSG.KC.IntLines CFSG.KC.LQT.Cov
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CertificateChecks.KernelLC.HeFix

@[expose] def strsC : List (List Char) :=
  [heE25WXStr.toList, heE25WYStr.toList, heE25WM1Str.toList, heE25WM2Str.toList,
   heE25WM3Str.toList, heE25WM4Str.toList, heE25WM5Str.toList, heE25WH0Str.toList,
   heE25WH1Str.toList, heE25WHUStr.toList]

theorem strs : (strsC.all fun l => (intsSK (tokK l)).isSome) = true := by
  unfold strsC
  str_lits heE25WXStr
  str_lits heE25WYStr
  str_lits heE25WM1Str
  str_lits heE25WM2Str
  str_lits heE25WM3Str
  str_lits heE25WM4Str
  str_lits heE25WM5Str
  str_lits heE25WH0Str
  str_lits heE25WH1Str
  str_lits heE25WHUStr
  simp only [String.toList_ofList]
  quickRfl

theorem wX : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WXStr.toList)
    (W 0) (W 1) = true := by
  str_lits heE25WXStr
  simp only [String.toList_ofList]
  quickRfl

theorem wY : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WYStr.toList)
    (W 2) (W 3) = true := by
  str_lits heE25WYStr
  simp only [String.toList_ofList]
  quickRfl

theorem wM1 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WM1Str.toList)
    (W 4) (W 5) = true := by
  str_lits heE25WM1Str
  simp only [String.toList_ofList]
  quickRfl

theorem wM2 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WM2Str.toList)
    (W 6) (W 7) = true := by
  str_lits heE25WM2Str
  simp only [String.toList_ofList]
  quickRfl

theorem wM3 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WM3Str.toList)
    (W 8) (W 9) = true := by
  str_lits heE25WM3Str
  simp only [String.toList_ofList]
  quickRfl

theorem wM4 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WM4Str.toList)
    (W 10) (W 11) = true := by
  str_lits heE25WM4Str
  simp only [String.toList_ofList]
  quickRfl

theorem wM5 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WM5Str.toList)
    (W 12) (W 13) = true := by
  str_lits heE25WM5Str
  simp only [String.toList_ofList]
  quickRfl

theorem wH0 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WH0Str.toList)
    (W 14) (W 15) = true := by
  str_lits heE25WH0Str
  simp only [String.toList_ofList]
  quickRfl

theorem wH1 : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WH1Str.toList)
    (W 16) (W 17) = true := by
  str_lits heE25WH1Str
  simp only [String.toList_ofList]
  quickRfl

theorem wHU : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] (lineInts heE25WHUStr.toList)
    (W 18) (W 19) = true := by
  str_lits heE25WHUStr
  simp only [String.toList_ofList]
  quickRfl

end CFSG.KD.W4E.HeE25

end
