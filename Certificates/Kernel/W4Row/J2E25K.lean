module

public import Certificates.Data.Kernel.W4Row.E25K
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.W4RowJ2E25
public import Certificates.Kernel.Sporadic.OddCore.J2PChain
public import Certificates.Kernel.Sporadic.OddCore.J2Cent
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 400000

namespace CFSG.KD.W4E.J2E25

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.W4E CFSG.KC.IntLines CFSG.KC.LQT.Cov
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CertificateChecks.KernelSpor

@[expose] def strsC : List (List Char) :=
  [j2E25WXStr.toList, j2E25WYStr.toList, j2E25WHBStr.toList, j2E25WHAStr.toList,
   j2E25WM0Str.toList, j2E25WM1Str.toList, j2E25WM2Str.toList, j2E25WM3Str.toList,
   j2E25WM4Str.toList, j2E25WM5Str.toList, j2E25WM6Str.toList, j2E25WM7Str.toList,
   j2E25WM8Str.toList, j2E25WM9Str.toList, j2E25WM10Str.toList, j2E25WM11Str.toList]

theorem strs : (strsC.all fun l => (intsSK (tokK l)).isSome) = true := by
  unfold strsC
  str_lits j2E25WXStr
  str_lits j2E25WYStr
  str_lits j2E25WHBStr
  str_lits j2E25WHAStr
  str_lits j2E25WM0Str
  str_lits j2E25WM1Str
  str_lits j2E25WM2Str
  str_lits j2E25WM3Str
  str_lits j2E25WM4Str
  str_lits j2E25WM5Str
  str_lits j2E25WM6Str
  str_lits j2E25WM7Str
  str_lits j2E25WM8Str
  str_lits j2E25WM9Str
  str_lits j2E25WM10Str
  str_lits j2E25WM11Str
  simp only [String.toList_ofList]
  quickRfl

theorem pack : ep2PackK 315 9 5 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (J2CentT.F 17)
    (J2CentT.F 31) j2E25PartIdx (lineInts j2E25WXStr.toList) (lineInts j2E25WYStr.toList)
    (lineInts j2E25WHBStr.toList) (lineInts j2E25WHAStr.toList)
    [lineInts j2E25WM0Str.toList, lineInts j2E25WM1Str.toList, lineInts j2E25WM2Str.toList,
     lineInts j2E25WM3Str.toList, lineInts j2E25WM4Str.toList, lineInts j2E25WM5Str.toList,
     lineInts j2E25WM6Str.toList, lineInts j2E25WM7Str.toList, lineInts j2E25WM8Str.toList,
     lineInts j2E25WM9Str.toList, lineInts j2E25WM10Str.toList, lineInts j2E25WM11Str.toList] =
    true := by
  str_lits j2E25WXStr
  str_lits j2E25WYStr
  str_lits j2E25WHBStr
  str_lits j2E25WHAStr
  str_lits j2E25WM0Str
  str_lits j2E25WM1Str
  str_lits j2E25WM2Str
  str_lits j2E25WM3Str
  str_lits j2E25WM4Str
  str_lits j2E25WM5Str
  str_lits j2E25WM6Str
  str_lits j2E25WM7Str
  str_lits j2E25WM8Str
  str_lits j2E25WM9Str
  str_lits j2E25WM10Str
  str_lits j2E25WM11Str
  simp only [String.toList_ofList]
  quickRfl

theorem tc3 : mcP 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] [J2CentT.F 9] [J2CentT.F 9]
    j2Outer3Words j2Outer3Prog [J2P.S 0, J2P.S 1] = true := by
  quickRfl

end CFSG.KD.W4E.J2E25

end
