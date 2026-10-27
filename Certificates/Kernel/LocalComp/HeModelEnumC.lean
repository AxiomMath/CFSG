module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

namespace CertificateChecks.KernelLC.HeModelEnum

meta def cGens : Array (Array Nat) := CFSG.ComponentClassification.AS81.HeTri.hePCGens.toArray

meta def cRun : Array (Array Nat) × Array (Array Nat) := CFSG.KC.BfsGen.search 32 6 cGens

meta def cPts : Array (Array Nat) := cRun.1

meta def cRows : Array (Array Nat) := cRun.2

meta def cOrder : Array (Array Nat) :=
  let tv := cPts.map (CFSG.KS.RawGen.pack 6)
  ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!).map fun i => #[i]

meta def cCounts : Array (Array Nat) :=
  (Array.range 17).map fun s =>
    #[((cRows.extract 0 (1344 * s)).foldl (fun m r => r.foldl max m) 0 + 1)]

end CertificateChecks.KernelLC.HeModelEnum

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.HeMC.G CertificateChecks.KernelLC.HeModelEnum.cGens 6
#kmisc_packarrs CertificateChecks.KernelLC.HeMC.T CertificateChecks.KernelLC.HeModelEnum.cPts 6
#kmisc_packarrs CertificateChecks.KernelLC.HeMC.E CertificateChecks.KernelLC.HeModelEnum.cRows 16
#kmisc_packarrs CertificateChecks.KernelLC.HeMC.S CertificateChecks.KernelLC.HeModelEnum.cOrder 32
#kmisc_packarrs CertificateChecks.KernelLC.HeMC.C CertificateChecks.KernelLC.HeModelEnum.cCounts 32

namespace CertificateChecks.KernelLC.HeMC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] def ng : Nat := 12

@[expose] def N : Nat := 21504

@[expose] noncomputable def cs (s : Nat) : Bool := canonSl 32 6 T 1344 s

@[expose] noncomputable def rs (s : Nat) : Bool := runSl 32 6 ng G T E 1344 C s

theorem kHead : (szOK 32 6 && allN ng (fun k => canonK 32 6 (mask 6) (Nat.mul 32 6) (G k)) &&
    Nat.beq (T 0) (pidn 32 6) && Nat.beq (C 0) 1 && Nat.beq (C 16) N) = true := by quickRfl

theorem kDist : distinctK N T S = true := by quickRfl

end CertificateChecks.KernelLC.HeMC

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.HeMC.cs 0 16
#kon_join CertificateChecks.KernelLC.HeMC.csAll CertificateChecks.KernelLC.HeMC.cs 16
#kon_slices CertificateChecks.KernelLC.HeMC.rs 0 16
#kon_join CertificateChecks.KernelLC.HeMC.rsAll CertificateChecks.KernelLC.HeMC.rs 16

namespace CertificateChecks.KernelLC.HeMC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

theorem ok : bfsK 32 6 ng G N T E S = true := by
  have k := kHead
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := k
  exact bfsK_of_slices (L := 1344) (K := 16) (C := C) rfl (by decide) h1 h2 csAll h3 kDist
    (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) rsAll

end CertificateChecks.KernelLC.HeMC

end
