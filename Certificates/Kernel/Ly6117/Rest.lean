module

public import Certificates.Kernel.Ly6117.Data
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLitToList

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy6117

open CFSG.KD.Ly6117 CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.KC.StrLitToList

theorem relLearned : allK G GI modularLearned = true := by
  simp only [modularLearned, modularLearnedStrings, List.map_cons, List.map_nil, parseWord,
    strLitToList]
  quickRfl

theorem relD : allK G GI modularD = true := by
  simp only [modularD, modularD1, modularD2, modularD3, List.map_cons, List.map_nil, parseWord,
    strLitToList]
  quickRfl

end CertificateChecks.KernelLy6117

end
