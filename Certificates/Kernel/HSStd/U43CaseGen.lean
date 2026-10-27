module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelHSStd.U43CaseGen

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.LieType.Multipliers.U43
open CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 820

meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 820 a

meta def tabsM (a : Array CFSG.Sporadic.Th.Native.Table) : Array (Array Nat) := a.map CFSG.Sporadic.SmallOddCore.Native.natArr

meta def inM (d : CaseData) : Array (Array Nat) :=
  #[CFSG.Sporadic.SmallOddCore.Native.natArr d.Tt, CFSG.Sporadic.SmallOddCore.Native.natArr d.y0] ++
    tabsM d.cg ++ tabsM d.yg ++ #[tabA, tabB, phiArr, deltaArr]

meta def inIM (d : CaseData) : Array (Array Nat) := (inM d).map invM

meta def cosM (d : CaseData) : Array (Array Nat) := (inM d).mapIdx fun i x =>
  if 2 ≤ i ∧ i < 2 + d.cg.size + d.yg.size then
    #[(d.ks.find? fun k =>
      inP (CFSG.Monster.B.Co2.Native.compA 820 x (invM (tArr k)))).getD 0]
  else #[0]

meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 820 idM gs[j]! t) gs.size idM 50000).tabs

meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invM).map fun g => comp 820 x g).flatten

meta def idsOf (gs : Array (Array Nat)) : Array (Array Nat) := Array.replicate gs.size idM

meta def gGM (d : CaseData) : Array (Array Nat) := tabsM d.gensG
meta def gGIM (d : CaseData) : Array (Array Nat) := (gGM d).map invM
meta def cgM (d : CaseData) : Array (Array Nat) := tabsM d.cg
meta def cgIM (d : CaseData) : Array (Array Nat) := (cgM d).map invM
meta def ygM (d : CaseData) : Array (Array Nat) := tabsM d.yg

meta def posIn (L : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:L.size] do
    m := m.insert L[i]! i
  return m

meta def cyRec (d : CaseData) : Array (Array Nat) :=
  let g := cgM d
  (bfs (fun j t => conjTab 820 g[j]! (invM g[j]!) t) g.size
    (CFSG.Sporadic.SmallOddCore.Native.natArr d.y0) 50000).tabs

meta def coverM (d : CaseData) : Array (Array Nat) :=
  let m := posIn (cyRec d)
  (recOf (cgM d)).map fun x =>
    #[if comp 820 x (comp 820 x x) == idM && x != idM then m.getD x 0 else 0]

end CertificateChecks.KernelHSStd.U43CaseGen

end
