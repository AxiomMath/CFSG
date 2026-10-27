module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

namespace CertificateChecks.KernelLC.B0Suz

meta def matGens : Array (Array Nat) := CFSG.ComponentClassification.AS81.SuzB0.matTabs

meta def matRun : Array (Array Nat) × Array (Array Nat) := CFSG.KC.BfsGen.search 64 7 matGens

meta def matPts : Array (Array Nat) := matRun.1

meta def matRows : Array (Array Nat) := matRun.2

meta def matOrder : Array (Array Nat) :=
  let tv := matPts.map (CFSG.KS.RawGen.pack 7)
  ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!).map fun i => #[i]

meta def matCounts : Array (Array Nat) :=
  (Array.range 17).map fun s =>
    #[((matRows.extract 0 (1620 * s)).foldl (fun m r => r.foldl max m) 0 + 1)]

end CertificateChecks.KernelLC.B0Suz

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.SuzB0M.G CertificateChecks.KernelLC.B0Suz.matGens 7
#kmisc_packarrs CertificateChecks.KernelLC.SuzB0M.T CertificateChecks.KernelLC.B0Suz.matPts 7
#kmisc_packarrs CertificateChecks.KernelLC.SuzB0M.E CertificateChecks.KernelLC.B0Suz.matRows 16
#kmisc_packarrs CertificateChecks.KernelLC.SuzB0M.S CertificateChecks.KernelLC.B0Suz.matOrder 32
#kmisc_packarrs CertificateChecks.KernelLC.SuzB0M.C CertificateChecks.KernelLC.B0Suz.matCounts 32

namespace CertificateChecks.KernelLC.SuzB0M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] def ng : Nat := 10

@[expose] def N : Nat := 25920

@[expose] noncomputable def cs (s : Nat) : Bool := canonSl 64 7 T 1620 s

@[expose] noncomputable def rs (s : Nat) : Bool := runSl 64 7 ng G T E 1620 C s

theorem kHead : (szOK 64 7 && allN ng (fun k => canonK 64 7 (mask 7) (Nat.mul 64 7) (G k)) &&
    Nat.beq (T 0) (pidn 64 7) && Nat.beq (C 0) 1 && Nat.beq (C 16) N) = true := by quickRfl

theorem kDist : distinctK N T S = true := by quickRfl

end CertificateChecks.KernelLC.SuzB0M

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.SuzB0M.cs 0 16
#kon_join CertificateChecks.KernelLC.SuzB0M.csAll CertificateChecks.KernelLC.SuzB0M.cs 16
#kon_slices CertificateChecks.KernelLC.SuzB0M.rs 0 16
#kon_join CertificateChecks.KernelLC.SuzB0M.rsAll CertificateChecks.KernelLC.SuzB0M.rs 16

namespace CertificateChecks.KernelLC.SuzB0M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

theorem ok : bfsK 64 7 ng G N T E S = true := by
  have k := kHead
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := k
  exact bfsK_of_slices (L := 1620) (K := 16) (C := C) rfl (by decide) h1 h2 csAll h3 kDist
    (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) rsAll

end CertificateChecks.KernelLC.SuzB0M

end
