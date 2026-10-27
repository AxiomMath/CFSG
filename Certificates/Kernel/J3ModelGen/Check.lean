module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Kernel.W4Model.Check
public import Certificates.Kernel.J3Fusion.Rels
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3ModelGen

open CFSG.KC.TabMatGrp CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
  CertificateChecks.KernelLC.J3Ops CertificateChecks.KernelW4Model CertificateChecks.KernelJ3Fusion

@[expose] noncomputable def pairs : List (List (Fin 7 × Bool) × List (Fin 2 × Bool)) :=
  j3Words.map (·, []) ++ [(wbWord.map zL, [(1, false)])]

theorem chk : grpK 80 SA.M SB.M 2 3 (segs.map natW) (pairs.map fun q => (natW q.1, natW q.2)) =
    true := by
  quickRfl

theorem neg : (!grpK 80 SA.M SB.M 2 3 (segs.map natW)
    ([(([(3, true)] : List (Fin 7 × Bool)), ([(1, false)] : List (Fin 2 × Bool)))].map
      fun q => (natW q.1, natW q.2))) = true := by
  quickRfl

end CertificateChecks.KernelJ3ModelGen

end
