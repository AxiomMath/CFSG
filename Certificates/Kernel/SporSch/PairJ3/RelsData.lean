module

public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Rels
meta import CFSG.Certificates.Kernel.Bounds.J3Alt.Rels

public section

namespace CertificateChecks.KernelSporSch.PJ3R

open CFSG.Monster.B.Co2.Native

meta def genM : Array (Array Nat) := #[CFSG.Sporadic.Schreier.j3StrongArrs[0]!,
  CFSG.Sporadic.Schreier.j3StrongArrs[1]!]

meta def valM (v : List (Nat × Bool)) : Array Nat :=
  v.foldr (fun l T => compA 6156 (if l.2 then genM[l.1]! else invCand 6156 genM[l.1]!) T)
    (idA 6156)

meta def ttM : Array (Array Nat) := (Array.range (16 * 8 + 1)).map fun j =>
  valM ((CFSG.KC.J3A.rels.getD (j / 16) []).drop (4 * (j % 16)))

end CertificateChecks.KernelSporSch.PJ3R

#kss_perms CertificateChecks.KernelSporSch.PJ3R.TT 13 CertificateChecks.KernelSporSch.PJ3R.ttM

end
