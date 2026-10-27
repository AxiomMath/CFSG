module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Data.GrSLitL34FactsSpMultJ3UC
public import Certificates.Kernel.LocalComp.J3Seeds
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPresLetters.F22224J

open CFSG.KC.TabMatGrp CertificateChecks.KernelLC.J3Ops CFSG.ComponentClassification.GSThmB.SpMult

@[expose] def segs : List (List (Fin 2 × Bool)) := [[(0, true)], [(1, true)], ucU, ucC]

@[expose] def shiftW (s : ℕ) (w : List (Fin 2 × Bool)) : List (Fin 4 × Bool) :=
  w.map fun l => (Fin.ofNat 4 (l.1.val + s), l.2)

@[expose] def words : List (List (Fin 4 × Bool)) :=
  ucABWords.map (shiftW 0) ++ gammaJ3Words.map (shiftW 2)

@[expose] def relPs (ws : List (List (Fin 4 × Bool))) :
    List (List (Fin 4 × Bool) × List (Fin 2 × Bool)) :=
  ws.map fun w => (w, [])

theorem chk : grpK 80 SA.M SB.M 2 3 (segs.map natW)
    ((relPs words).map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

end CertificateChecks.KernelPresLetters.F22224J

end
