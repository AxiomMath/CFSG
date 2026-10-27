module

public import Certificates.Kernel.OmegaEight.C3006D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTab CFSG.KC.CycTabW CFSG.LieType.Multipliers

theorem relsA : onesOKW 360 9 D.TA (rels.map (List.map codeW)) = true := by
  quickRfl

theorem commA : ((List.finRange 4).all fun i => eqOKW 360 9 D.TA ((commWords (pairs i)).map codeW)
    (fun x => fgW 9 D.TA (2 * i.val * 360 + x))) = true := by
  quickRfl

theorem genWordsA : ((List.finRange 8).all fun j =>
    eqOKW 360 9 D.TA ((genWords j).map codeW) (cycsK 360 (genCycles j))) = true := by
  quickRfl

theorem uA : onesOKW 360 9 D.TA [(uWord ++ uWord).map codeW] = true := by
  quickRfl

theorem tuA : eqOKW 360 9 D.TA (tuWord.map codeW)
    (fun x => (wordW 360 9 D.TA (uWord.map codeW) ((x + 240) % 360) + 120) % 360) = true := by
  quickRfl

end CertificateChecks.KernelO8.C3006

end
