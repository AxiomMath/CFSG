module

public import Certificates.Kernel.SporSch.PairHS.Chain
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels
meta import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels

public section

namespace CertificateChecks.KernelSporSch.PHSR

open CFSG.Monster.B.Co2.Native

meta def genM : Array (Array Nat) := #[CFSG.Sporadic.Schreier.hsStrongArrs[0]!,
  CFSG.Sporadic.Schreier.hsStrongArrs[1]!]

meta def valM (v : List (Nat × Bool)) : Array Nat :=
  v.foldr (fun l T => compA 3850 (if l.2 then genM[l.1]! else invCand 3850 genM[l.1]!) T)
    (idA 3850)

meta def ttM : Array (Array Nat) := (Array.range (10 * 13 + 1)).map fun j =>
  valM ((CFSG.KC.HSK.relsLit.getD (j / 10) []).drop (4 * (j % 10)))

end CertificateChecks.KernelSporSch.PHSR

#kss_perms CertificateChecks.KernelSporSch.PHSR.TT 12 CertificateChecks.KernelSporSch.PHSR.ttM

end
