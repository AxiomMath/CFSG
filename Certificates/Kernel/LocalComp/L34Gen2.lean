module

public import Certificates.Kernel.LocalComp.L34Gen
public meta import Certificates.Kernel.LocalComp.L34Gen

public section

namespace CertificateChecks.KernelLC.L34Gen

open CFSG.PSL3Four.Native
open CFSG.KS.RawGen (pack)

meta def posIn (L : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for k in [0:L.size] do
    m := m.insert L[k]! k
  return m

meta def ones (a : Array (Array Nat)) : Array (Array Nat) := a.map fun x => #[pack 6 x]

meta def giP : Array (Array Nat) := ones (gTabs.map (invTab 42))

meta def rP : Array (Array Nat) := ones (rTabs ())

meta def sPts : Array (Array Nat) := sRun.1

meta def normW : Array (Array Nat) :=
  let idx := posIn sPts
  #[#[pack 16 ((Array.range 18).flatMap fun ji =>
    let g := gTabs[ji / 3]!
    let gi := invTab 42 g
    let s := gensS[ji % 3]!
    #[idx.getD (comp 42 (comp 42 g s) gi) 0, idx.getD (comp 42 (comp 42 gi s) g) 0])]]

meta def oPts (i : Nat) : Array (Array Nat) := (oRun (rTabs ())[i]!).1

meta def coverW : Array (Array Nat) :=
  let maps := (Array.range 4).map fun o => posIn (oPts o)
  let e := idTab 42
  chunks 16 (rRun.1.map fun x =>
    if x != e && comp 42 x x == e then
      ((Array.range 4).findSome? fun o => (maps[o]!.get? x).map (o * 2048 + ·)).getD 0
    else 0)

meta def cIdx (i : Nat) : Array Nat :=
  let r := (rTabs ())[i]!
  (Array.range sPts.size).filter fun j => comp 42 sPts[j]! r == comp 42 r sPts[j]!

meta def cList (i : Nat) : Array (Array Nat) := (cIdx i).map (sPts[·]!)

meta def cIdxP (i : Nat) : Array (Array Nat) := (cIdx i).map fun j => #[j]

meta def prodRows (C : Array (Array Nat)) : Array (Array Nat) :=
  let idx := posIn C
  C.map fun x => #[pack 8 (C.map fun y => idx.getD (comp 42 x y) 0)]

meta def conjRows (C : Array (Array Nat)) : Array (Array Nat) :=
  let idx := posIn C
  C.map fun x => #[pack 8 (C.map fun y => idx.getD (comp 42 (comp 42 y x) (invTab 42 y)) 0)]

meta def classP (C : Array (Array Nat)) (sizes : Array Nat) : Array (Array Nat) :=
  let cd := classData 42 C sizes
  #[#[pack 8 cd.lab], #[pack 8 cd.reps], #[pack 8 cd.wit], #[pack 8 sizes]]

meta def der (T : Array (Array Nat)) : Array (Array Nat) × Array (Nat × Nat × Nat × Nat) :=
  derivedData 42 T (T.map (invTab 42))

meta def dProd (D : Array (Array Nat)) : Array (Array Nat) := prodRows D

meta def dMisc (D : Array (Array Nat)) (W : Array (Nat × Nat × Nat × Nat)) : Array (Array Nat) :=
  let idx := posIn D
  #[#[pack 8 (D.map fun x => idx.getD (invTab 42 x) 0)],
    #[pack 32 (W.map fun (a, b, c, d) => a + (b <<< 8) + (c <<< 16) + (d <<< 24))]]

meta def commRows (T D : Array (Array Nat)) : Array (Array Nat) :=
  let idx := posIn D
  T.map fun x => #[pack 8 (T.map fun y =>
    idx.getD (commTab 42 x y (invTab 42 x) (invTab 42 y)) 0)]

meta def c4 : Array (Array Nat) := cList 3
meta def d1 : Array (Array Nat) := (der c4).1
meta def d2 : Array (Array Nat) := (der d1).1
meta def d3 : Array (Array Nat) := (der d2).1

meta def d1P : Array (Array Nat) := ones d1
meta def d2P : Array (Array Nat) := ones d2
meta def d3P : Array (Array Nat) := ones d3
meta def c4I : Array (Array Nat) := ones (c4.map (invTab 42))
meta def d1I : Array (Array Nat) := ones (d1.map (invTab 42))
meta def d2I : Array (Array Nat) := ones (d2.map (invTab 42))
meta def d1Prod : Array (Array Nat) := dProd d1
meta def d2Prod : Array (Array Nat) := dProd d2
meta def d3Prod : Array (Array Nat) := dProd d3
meta def d1Misc : Array (Array Nat) := dMisc d1 (der c4).2
meta def d2Misc : Array (Array Nat) := dMisc d2 (der d1).2
meta def d3Misc : Array (Array Nat) := dMisc d3 (der d2).2
meta def d1Comm : Array (Array Nat) := commRows c4 d1
meta def d2Comm : Array (Array Nat) := commRows d1 d2
meta def d3Comm : Array (Array Nat) := commRows d2 d3

meta def c2 : Array (Array Nat) := cList 1
meta def c3 : Array (Array Nat) := cList 2
meta def c2I : Array (Array Nat) := ones (c2.map (invTab 42))
meta def c3I : Array (Array Nat) := ones (c3.map (invTab 42))
meta def c2Q : Array (Array Nat) := prodRows c2
meta def c3Q : Array (Array Nat) := prodRows c3
meta def c2P : Array (Array Nat) := conjRows c2
meta def c3P : Array (Array Nat) := conjRows c3
meta def c2L : Array (Array Nat) := classP c2 sizes₂
meta def c3L : Array (Array Nat) := classP c3 sizes₃

meta def cP (i : Nat) : Array (Array Nat) := ones (cList i)
meta def c1P : Array (Array Nat) := cP 0
meta def c2P' : Array (Array Nat) := cP 1
meta def c3P' : Array (Array Nat) := cP 2
meta def c4P : Array (Array Nat) := cP 3
meta def c1X : Array (Array Nat) := cIdxP 0
meta def c2X : Array (Array Nat) := cIdxP 1
meta def c3X : Array (Array Nat) := cIdxP 2
meta def c4X : Array (Array Nat) := cIdxP 3

meta def o0 := oLay 0
meta def o1 := oLay 1
meta def o2 := oLay 2
meta def o3 := oLay 3
meta def o0T : Array (Array Nat) := o0.1
meta def o0E : Array (Array Nat) := o0.2.1
meta def o0S : Array (Array Nat) := o0.2.2.1
meta def o0SI : Array (Array Nat) := o0.2.2.2.1
meta def o1T : Array (Array Nat) := o1.1
meta def o1E : Array (Array Nat) := o1.2.1
meta def o1S : Array (Array Nat) := o1.2.2.1
meta def o1SI : Array (Array Nat) := o1.2.2.2.1
meta def o2T : Array (Array Nat) := o2.1
meta def o2E : Array (Array Nat) := o2.2.1
meta def o2S : Array (Array Nat) := o2.2.2.1
meta def o2SI : Array (Array Nat) := o2.2.2.2.1
meta def o3T : Array (Array Nat) := o3.1
meta def o3E : Array (Array Nat) := o3.2.1
meta def o3S : Array (Array Nat) := o3.2.2.1
meta def o3SI : Array (Array Nat) := o3.2.2.2.1

end CertificateChecks.KernelLC.L34Gen

end
