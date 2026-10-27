module

public import Certificates.Kernel.Ly6117.Data
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLitToList

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy6117

open CFSG.KD.Ly6117 CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.KC.StrLitToList

theorem relCore : allK G GI Rcore107 = true := by
  simp only [Rcore107, core107Strings, List.map_cons, List.map_nil, parseWord, strLitToList]
  quickRfl

end CertificateChecks.KernelLy6117

end
