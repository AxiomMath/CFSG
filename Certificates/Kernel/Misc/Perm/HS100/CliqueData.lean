module

public import Certificates.Kernel.Misc.Perm.BlocksCmd
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData

public section

namespace CertificateChecks.KernelMisc.HS100.Clique

open CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.KS.RawGen

meta def pts : Array (Array Nat) := (CFSG.KC.ConjOrbGen.search 100 7 hsGens x3).1

meta def adj (p q : Array Nat) : Bool :=
  let r := comp 100 p q
  r != Array.range 100 && comp 100 r r == Array.range 100

meta def nb : Array Nat := (Array.range pts.size).filter fun i => adj x3 pts[i]!

meta def inv : Array Nat := Id.run do
  let mut r := Array.replicate pts.size 0
  for j in [0:nb.size] do
    r := r.set! nb[j]! j
  return r

end CertificateChecks.KernelMisc.HS100.Clique

end

#kmisc_blocks CertificateChecks.KernelMisc.HS100.Clique.NB CertificateChecks.KernelMisc.HS100.Clique.nb 20
#kmisc_blocks CertificateChecks.KernelMisc.HS100.Clique.INV
  CertificateChecks.KernelMisc.HS100.Clique.inv 9
