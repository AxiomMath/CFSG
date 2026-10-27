module

public import Certificates.Data.Kernel.W4Row.InvPackK
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.W4RowRuE25
public import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 400000

namespace CFSG.KD.W4E.RuE25

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.W4E CFSG.KC.IntLines
  CFSG.KC.LQT.Cov CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
  CertificateChecks.KernelSporSch.RuG

@[expose] def strsC : List (List Char) :=
  [ruE25WYStr.toList, ruE25WWStr.toList, ruE25WHStr.toList]

theorem strs : (strsC.all fun l => (intsSK (tokK l)).isSome) = true := by
  unfold strsC
  str_lits ruE25WYStr
  str_lits ruE25WWStr
  str_lits ruE25WHStr
  simp only [String.toList_ofList]
  quickRfl

theorem pack : invFullK 4060 12 5 6 [A0, A1] [A0I, A1I] (pcomp 4060 12 (mask 12) A1 A1)
    (pcomp 4060 12 (mask 12) A1 A1) (lineInts ruE25WYStr.toList) (lineInts ruE25WWStr.toList)
    (lineInts ruE25WHStr.toList) ruE25Conj = true := by
  str_lits ruE25WYStr
  str_lits ruE25WWStr
  str_lits ruE25WHStr
  simp only [String.toList_ofList]
  quickRfl

end CFSG.KD.W4E.RuE25

end
