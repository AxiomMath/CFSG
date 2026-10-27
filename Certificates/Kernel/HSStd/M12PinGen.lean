module

public import Certificates.Kernel.LocalComp.L34Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12Data
public meta import Certificates.Kernel.LocalComp.L34Gen
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12Data

public section

namespace CertificateChecks.KernelHSStd.M12PinGen

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HSStd.HFI CertificateChecks.KernelLC.L34Gen
open CFSG.KS.RawGen (pack)

meta def mRun : Array (Array Nat) × Array (Array Nat) :=
  searchSt 2 (fun k t => comp 12 m12Gens[k]! t) (idTab 12)

meta def mLay := layout mRun.1 mRun.2 17 1440

meta def mT : Array (Array Nat) := mLay.1
meta def mE : Array (Array Nat) := mLay.2.1
meta def mS : Array (Array Nat) := mLay.2.2.1
meta def mSI : Array (Array Nat) := mLay.2.2.2.1
meta def mC : Array (Array Nat) := mLay.2.2.2.2

meta def gP : Array (Array Nat) := m12Gens.map fun g => #[pack 6 g]
meta def giP : Array (Array Nat) := m12Gens.map fun g => #[pack 6 (invTab 12 g)]

meta def oRun (r : Array Nat) : Array (Array Nat) × Array (Array Nat) :=
  searchSt 2 (fun k t => comp 12 (comp 12 m12Gens[k]! t) (invTab 12 m12Gens[k]!)) r

meta def aLay := let o := oRun m12a₀T; layout o.1 o.2 10 o.1.size
meta def bLay := let o := oRun m12b₀T; layout o.1 o.2 10 o.1.size

meta def aT : Array (Array Nat) := aLay.1
meta def aE : Array (Array Nat) := aLay.2.1
meta def aS : Array (Array Nat) := aLay.2.2.1
meta def aSI : Array (Array Nat) := aLay.2.2.2.1
meta def bT : Array (Array Nat) := bLay.1
meta def bE : Array (Array Nat) := bLay.2.1
meta def bS : Array (Array Nat) := bLay.2.2.1
meta def bSI : Array (Array Nat) := bLay.2.2.2.1

meta def posIn (L : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:L.size] do
    m := m.insert L[i]! i
  return m

meta def coverW : Array (Array Nat) :=
  let maps := #[posIn (oRun m12a₀T).1, posIn (oRun m12b₀T).1]
  let e := idTab 12
  chunks 16 (mRun.1.map fun x =>
    if x != e && comp 12 x x == e then
      ((Array.range 2).findSome? fun o => (maps[o]!.get? x).map (o * 1024 + ·)).getD 0
    else 0)

meta def abX : Array (Array Nat) :=
  let m := posIn mRun.1
  #[#[m.getD m12a₀T 0], #[m.getD m12b₀T 0]]

meta def cIdx : Array Nat :=
  let pts := mRun.1
  (Array.range pts.size).filter fun j => comp 12 pts[j]! m12a₀T == comp 12 m12a₀T pts[j]!

meta def cX : Array (Array Nat) := cIdx.map fun j => #[j]
meta def cP : Array (Array Nat) := cIdx.map fun j => #[pack 6 mRun.1[j]!]

meta def cCnt : Array (Array Nat) :=
  (Array.range 67).map fun s => #[(cIdx.filter (· < 1440 * s)).size]

meta def hW : Array (Array Nat) :=
  let pts := mRun.1
  let a := m12a₀T
  cIdx.map fun i =>
    let x := pts[i]!
    let ax := comp 12 a x
    #[((Array.range pts.size).find? fun j =>
      comp 12 pts[j]! a == comp 12 x pts[j]! && comp 12 pts[j]! x == comp 12 ax pts[j]!).getD 0]

end CertificateChecks.KernelHSStd.M12PinGen

end
