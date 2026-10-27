module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableICheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Check
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableICheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Check
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.KD.HN1408.RecGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def idM : Array Nat := idTab 1408

meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 1408 a

meta def gensM (ws : List (List Nat)) : Array (Array Nat) := (ws.map fun w => natArr (tabW w)).toArray

meta def idsOf (gs : Array (Array Nat)) : Array (Array Nat) := Array.replicate gs.size idM

meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1408 idM gs[j]! t) gs.size idM 1000000).tabs

meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invM).map fun g => comp 1408 x g).flatten

meta def recOfN (n : Nat) (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab n (idTab n) gs[j]! t) gs.size (idTab n) 1000000).tabs

meta def clOfN (n : Nat) (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOfN n gs).map fun x => (gs ++ gs.map (CFSG.Monster.B.Co2.Native.invCand n)).map fun g =>
    comp n x g).flatten

meta def g7 : Array (Array Nat) := h1408Gens.toArray.map natArr
meta def g7I : Array (Array Nat) := g7.map invM

meta def clsOf (x : Array Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1408 g7[j]! g7I[j]! t) 7 x 1000000).tabs

meta def posIn (L : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:L.size] do
    m := m.insert L[i]! i
  return m

meta def posOf (L xs : Array (Array Nat)) : Array (Array Nat) :=
  let m := posIn L
  xs.map fun x => #[m.getD x L.size]

end CFSG.KD.HN1408.RecGen

end
