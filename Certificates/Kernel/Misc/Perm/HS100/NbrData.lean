module

public import Certificates.Kernel.Misc.Perm.BlocksCmd
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
public import CFSG.RankThree.Native.FiveKit
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
meta import CFSG.RankThree.Native.FiveKit
meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelMisc.HS100.Nbr

open CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.KS.RawGen

meta def src : Array (Array Nat) :=
  (CFSG.KC.ConjOrbGen.search 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.pGens
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.z0).1 ++
    (CFSG.KC.ConjOrbGen.search 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.pGens
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.u0).1

meta def cand : Array (Array Nat) := src.map (comp 100 (comp 100 x3 x3))

meta def cube3 (b : Array Nat) : Bool := comp 100 b (comp 100 b b) == Array.range 100

meta def nb : Array Nat := (Array.range cand.size).filter fun i => cube3 cand[i]!

meta def inv : Array Nat := Id.run do
  let mut r := Array.replicate cand.size 0
  for j in [0:nb.size] do
    r := r.set! nb[j]! j
  return r

meta def nlp : Array Nat := nb.map fun i => pack 7 cand[i]!

end CertificateChecks.KernelMisc.HS100.Nbr

end

#kmisc_blocks CertificateChecks.KernelMisc.HS100.Nbr.NLP CertificateChecks.KernelMisc.HS100.Nbr.nlp 700

#kmisc_blocks CertificateChecks.KernelMisc.HS100.Nbr.NBI CertificateChecks.KernelMisc.HS100.Nbr.nb 20
#kmisc_blocks CertificateChecks.KernelMisc.HS100.Nbr.INVI
  CertificateChecks.KernelMisc.HS100.Nbr.inv 9
