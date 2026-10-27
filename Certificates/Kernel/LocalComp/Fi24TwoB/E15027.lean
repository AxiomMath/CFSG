module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import Certificates.Kernel.Sporadic.Fi22.C2068
meta import Certificates.Kernel.Sporadic.Fi22.C3151

namespace CertificateChecks.KernelLC.Fi24BE

meta def gens : Array (Array Nat) :=
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NGens

meta def run : Array (Array Nat) × Array (Array Nat) := CFSG.KC.BfsGen.search 504 9 gens

meta def pts : Array (Array Nat) := run.1

meta def rows : Array (Array Nat) := run.2

meta def order : Array (Array Nat) :=
  let tv := pts.map (CFSG.KS.RawGen.pack 9)
  ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!).map fun i => #[i]

meta def counts : Array (Array Nat) :=
  (Array.range 1025).map fun s =>
    #[((rows.extract 0 (4 * s)).foldl (fun m r => r.foldl max m) 0 + 1)]

meta def keyOf (a : Array Nat) : Nat :=
  [4, 0, 1, 2, 3, 6].foldr (fun p acc => a[p]! + 504 * acc) 0

meta def keyOrder : List Nat :=
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelLC.Fi24BE

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.Fi24BN.G CertificateChecks.KernelLC.Fi24BE.gens 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BN.T CertificateChecks.KernelLC.Fi24BE.pts 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BN.E CertificateChecks.KernelLC.Fi24BE.rows 16
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BN.S CertificateChecks.KernelLC.Fi24BE.order 32
#kmisc_packarrs CertificateChecks.KernelLC.Fi24BN.C CertificateChecks.KernelLC.Fi24BE.counts 32
#kss_natlist CertificateChecks.KernelLC.Fi24BN.SKT CertificateChecks.KernelLC.Fi24BE.keyOrder

namespace CertificateChecks.KernelLC.Fi24BN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] def ng : Nat := 12

@[expose] def N : Nat := 4096

@[expose] noncomputable def SK : List Nat := (List.range 4096).map SKT

@[expose] noncomputable def cs (s : Nat) : Bool := canonSl 504 9 T 4 s

@[expose] noncomputable def rs (s : Nat) : Bool := runSl 504 9 ng G T E 4 C s

theorem kHead : (szOK 504 9 && allN ng (fun k => canonK 504 9 (mask 9) (Nat.mul 504 9) (G k)) &&
    Nat.beq (T 0) (pidn 504 9) && Nat.beq (C 0) 1 && Nat.beq (C 1024) N) = true := by quickRfl

theorem kDist : distinctK N T S = true := by quickRfl

theorem keys : keysSK 504 9 [4, 0, 1, 2, 3, 6] N T SK = true := by quickRfl

end CertificateChecks.KernelLC.Fi24BN

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.Fi24BN.cs 0 1024
#kon_join CertificateChecks.KernelLC.Fi24BN.csAll CertificateChecks.KernelLC.Fi24BN.cs 1024
#kon_slices CertificateChecks.KernelLC.Fi24BN.rs 0 1024
#kon_join CertificateChecks.KernelLC.Fi24BN.rsAll CertificateChecks.KernelLC.Fi24BN.rs 1024

namespace CertificateChecks.KernelLC.Fi24BN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

theorem ok : bfsK 504 9 ng G N T E S = true := by
  have k := kHead
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := k
  exact bfsK_of_slices (L := 4) (K := 1024) (C := C) rfl (by decide) h1 h2 csAll h3 kDist
    (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) rsAll

end CertificateChecks.KernelLC.Fi24BN

end
