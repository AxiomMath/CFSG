module

public import Certificates.Kernel.OmegaEight.C3006D
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.OmegaEight.C3006S
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTab CFSG.KC.CycTabW CFSG.LieType.Multipliers

theorem relsA : onesOKW 360 9 D.TA (rels.map (List.map codeW)) = true := by
  quickRfl

theorem commA : ((List.finRange 4).all fun i => eqOKW 360 9 D.TA ((commWords (pairs i)).map codeW)
    (fun x => fgW 9 D.TA (2 * i.val * 360 + x))) = true := by
  quickRfl

theorem genWordsA_0 :
    eqOKW 360 9 D.TA ((genWords 0).map codeW) (cycsS 360 (genCycles 0)) = true := by
  quickRfl

theorem genWordsA_1 :
    eqOKW 360 9 D.TA ((genWords 1).map codeW) (cycsS 360 (genCycles 1)) = true := by
  quickRfl

theorem genWordsA_2 :
    eqOKW 360 9 D.TA ((genWords 2).map codeW) (cycsS 360 (genCycles 2)) = true := by
  quickRfl

theorem genWordsA_3 :
    eqOKW 360 9 D.TA ((genWords 3).map codeW) (cycsS 360 (genCycles 3)) = true := by
  quickRfl

theorem genWordsA_4 :
    eqOKW 360 9 D.TA ((genWords 4).map codeW) (cycsS 360 (genCycles 4)) = true := by
  quickRfl

theorem genWordsA_5 :
    eqOKW 360 9 D.TA ((genWords 5).map codeW) (cycsS 360 (genCycles 5)) = true := by
  quickRfl

theorem genWordsA_6 :
    eqOKW 360 9 D.TA ((genWords 6).map codeW) (cycsS 360 (genCycles 6)) = true := by
  quickRfl

theorem genWordsA_7 :
    eqOKW 360 9 D.TA ((genWords 7).map codeW) (cycsS 360 (genCycles 7)) = true := by
  quickRfl

theorem genWordsA : ((List.finRange 8).all fun j =>
    eqOKW 360 9 D.TA ((genWords j).map codeW) (cycsK 360 (genCycles j))) = true := by
  simp only [← cycsS_eq, List.all_eq_true, List.mem_finRange, true_implies]
  intro j
  fin_cases j
  exacts [genWordsA_0, genWordsA_1, genWordsA_2, genWordsA_3, genWordsA_4, genWordsA_5,
    genWordsA_6, genWordsA_7]

theorem uA : onesOKW 360 9 D.TA [(uWord ++ uWord).map codeW] = true := by
  quickRfl

theorem tuA : eqOKW 360 9 D.TA (tuWord.map codeW)
    (fun x => (wordW 360 9 D.TA (uWord.map codeW) ((x + 240) % 360) + 120) % 360) = true := by
  quickRfl

end CertificateChecks.KernelO8.C3006

end
