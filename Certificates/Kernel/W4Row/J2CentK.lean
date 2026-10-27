module

public import Certificates.Data.Kernel.W4Row.CentPairK
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.W4RowJ2Cent
public import Certificates.Kernel.Sporadic.OddCore.J2PChain
public import Certificates.Kernel.LocalQT.SV.C4127D
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 400000

namespace CFSG.KD.W4C.J2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.LQT.JX CFSG.KC.W4C CFSG.KC.IntLines
  CFSG.KC.LQT.Cov CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
  CertificateChecks.KernelSpor CFSG.KD.LQT.C4127

@[expose] def strsC : List (List Char) :=
  [j2CentWZ1Str.toList, j2CentWX1Str.toList, j2CentWZ2Str.toList, j2CentWX2Str.toList,
   j2CentWZ7Str.toList, j2CentWX7Str.toList, j2CentWZ54Str.toList, j2CentWX54Str.toList,
   j2CentWZ58Str.toList, j2CentWX58Str.toList, j2CentWZ165Str.toList, j2CentWX165Str.toList]

theorem strs : (strsC.all fun l => (intsSK (tokK l)).isSome) = true := by
  unfold strsC
  str_lits j2CentWZ1Str
  str_lits j2CentWX1Str
  str_lits j2CentWZ2Str
  str_lits j2CentWX2Str
  str_lits j2CentWZ7Str
  str_lits j2CentWX7Str
  str_lits j2CentWZ54Str
  str_lits j2CentWX54Str
  str_lits j2CentWZ58Str
  str_lits j2CentWX58Str
  str_lits j2CentWZ165Str
  str_lits j2CentWX165Str
  simp only [String.toList_ofList]
  quickRfl

theorem cp1 : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E 1)
    (lineInts j2CentWZ1Str.toList) (lineInts j2CentWX1Str.toList) j2CentProg1
    [J2P.S 0, J2P.S 1] = true := by
  str_lits j2CentWZ1Str
  str_lits j2CentWX1Str
  simp only [String.toList_ofList]
  quickRfl

theorem cp2 : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E 2)
    (lineInts j2CentWZ2Str.toList) (lineInts j2CentWX2Str.toList) j2CentProg2
    [J2P.S 0, J2P.S 1] = true := by
  str_lits j2CentWZ2Str
  str_lits j2CentWX2Str
  simp only [String.toList_ofList]
  quickRfl

theorem cp7 : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E 7)
    (lineInts j2CentWZ7Str.toList) (lineInts j2CentWX7Str.toList) j2CentProg7
    [J2P.S 0, J2P.S 1] = true := by
  str_lits j2CentWZ7Str
  str_lits j2CentWX7Str
  simp only [String.toList_ofList]
  quickRfl

theorem cp54 : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E 54)
    (lineInts j2CentWZ54Str.toList) (lineInts j2CentWX54Str.toList) j2CentProg54
    [J2P.S 0, J2P.S 1] = true := by
  str_lits j2CentWZ54Str
  str_lits j2CentWX54Str
  simp only [String.toList_ofList]
  quickRfl

theorem cp58 : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E 58)
    (lineInts j2CentWZ58Str.toList) (lineInts j2CentWX58Str.toList) j2CentProg58
    [J2P.S 0, J2P.S 1] = true := by
  str_lits j2CentWZ58Str
  str_lits j2CentWX58Str
  simp only [String.toList_ofList]
  quickRfl

theorem cp165 : cpK 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] (SY.E 17) (SY.E 165)
    (lineInts j2CentWZ165Str.toList) (lineInts j2CentWX165Str.toList) j2CentProg165
    [J2P.S 0, J2P.S 1] = true := by
  str_lits j2CentWZ165Str
  str_lits j2CentWX165Str
  simp only [String.toList_ofList]
  quickRfl

theorem zc : zcK 8 256 17 IX.MR = true := by quickRfl

theorem cov : covK 8 256 17 IX.MR IX.IT [1, 2, 7, 54, 58, 165] = true := by quickRfl

end CFSG.KD.W4C.J2Cent

end
