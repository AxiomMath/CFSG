module

public import Certificates.Data.Kernel.TabMatGrp
public import CFSG.Sporadic.Recognition.J3MultiplierWords
public import Certificates.Kernel.LocalComp.J3Seeds
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3Mult.Words24090

open CFSG.KC.TabMatGrp CertificateChecks.KernelLC.J3Ops CFSG.Sporadic.Recognition.J3Multiplier

@[expose] def relPs (ws : List (List (Fin 2 × Bool))) :
    List (List (Fin 2 × Bool) × List (Fin 2 × Bool)) :=
  ws.map fun w => (w, [])

theorem ch24090_words : grpK 80 SA.M SB.M 2 3 (genWords.map natW)
    ((relPs checkWords).map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

end CertificateChecks.KernelJ3Mult.Words24090

end
