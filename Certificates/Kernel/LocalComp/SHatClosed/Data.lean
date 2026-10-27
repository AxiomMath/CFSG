module

public import Certificates.Kernel.LocalComp.SHatClosed.Enum
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.SHatClosedK
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs
meta import Certificates.Kernel.LocalComp.BfsGen

namespace CertificateChecks.KernelLC.SHatClosed

meta def pts : Array (Array Nat) :=
  (CFSG.KC.BfsGen.search 64 7 #[CFSG.ComponentClassification.AS81.Census.f2perm
    CFSG.ComponentClassification.AS81.Census.g1M, CFSG.ComponentClassification.AS81.Census.f2perm
    CFSG.ComponentClassification.AS81.Census.g2M]).1

meta def cmp (t u : Array Nat) : Array Nat := u.map fun x => t[x]!

meta def idt : Array Nat := (List.range 64).toArray

meta def invIdx : Array Nat :=
  (Array.range pts.size).filter fun i => cmp pts[i]! pts[i]! == idt && pts[i]! != idt

meta def invs : Array (Array Nat) := invIdx.map fun i => pts[i]!

meta def mI : Nat := invs.size

meta def comm : Array (Array Bool) :=
  invs.map fun a => invs.map fun b => cmp a b == cmp b a

meta def idxOf : Std.HashMap (Array Nat) Nat :=
  (Array.range mI).foldl (fun m j => m.insert invs[j]! j) {}

meta def iRows : Array (Array Nat) := invIdx.map fun i => #[i]

meta def cmRows : Array (Array Nat) := comm.map fun r => r.map fun b => if b then 1 else 0

meta def fxRows : Array (Array Nat) :=
  invs.map fun a => (Array.range 64).map fun p => if a[p]! == p then 1 else 0

meta def ptRows : Array (Array Nat) :=
  (Array.range mI).map fun j => (Array.range mI).map fun k =>
    if (comm[j]!)[k]! && j != k then idxOf.getD (cmp invs[j]! invs[k]!) 0 else 0

meta def ciL : Array (Array Nat) :=
  (Array.range mI).map fun i => (Array.range mI).filter fun j => (comm[i]!)[j]!

meta def cnRows : Array (Array Nat) := ciL.map fun c => #[c.size]

meta def cmcRows : Array (Array Nat) :=
  ciL.map fun c => c.foldl (fun acc l => acc ++ cmRows[l]! ++ Array.replicate (320 - mI) 0) #[]

meta def fxcRows : Array (Array Nat) := ciL.map fun c => c.foldl (fun acc l => acc ++ fxRows[l]!) #[]

end CertificateChecks.KernelLC.SHatClosed

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.SHatD.I CertificateChecks.KernelLC.SHatClosed.iRows 32
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.V CertificateChecks.KernelLC.SHatClosed.invs 7
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.CM CertificateChecks.KernelLC.SHatClosed.cmRows 1
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.FX CertificateChecks.KernelLC.SHatClosed.fxRows 1
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.PTR CertificateChecks.KernelLC.SHatClosed.ptRows 9
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.CN CertificateChecks.KernelLC.SHatClosed.cnRows 32
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.CIX CertificateChecks.KernelLC.SHatClosed.ciL 9
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.CMC CertificateChecks.KernelLC.SHatClosed.cmcRows 1
#kmisc_packarrs CertificateChecks.KernelLC.SHatD.FXC CertificateChecks.KernelLC.SHatClosed.fxcRows 1

namespace CertificateChecks.KernelLC.SHatD

open CFSG.KC.SHatClosed

@[expose] noncomputable def invC : Bool := invIdxK SHatL.N 315 SHatL.T I

@[expose] noncomputable def bindC : Bool := bindK 315 SHatL.T I V

@[expose] noncomputable def rowC (j : Nat) : Bool := rowK 315 V CM FX PTR j

@[expose] noncomputable def ciC (i : Nat) : Bool := ciK 315 CM FX CN CIX CMC FXC i

@[expose] noncomputable def f1C : Bool := f1K 315 FX

@[expose] noncomputable def f23C (i : Nat) : Bool := f23K CM FX PTR CN CIX CMC FXC i

end CertificateChecks.KernelLC.SHatD

end
