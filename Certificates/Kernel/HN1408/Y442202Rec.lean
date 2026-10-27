module

public import Certificates.Kernel.HN1408.Y442202Defs
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Y442202M

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Simple2S5

meta def tabN (t : CFSG.Sporadic.Th.Native.Table) : Array Nat := t.map UInt32.toNat
meta def idM : Array Nat := idTab 1408
meta def wM (w : List Nat) : Array Nat := tabN (tabW w)
meta def mulM (p q : Array Nat) : Array Nat := comp 1408 p q
meta def gensOf (ws : List (List Nat)) : Array (Array Nat) := (ws.map wM).toArray
meta def recOf (g : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1408 g[j]! idM t) g.size idM 4096).tabs

meta def wListM : List (List Nat) :=
  [sOne, sTwo, classz.rep, classaz.rep] ++ classz.centGens ++ classaz.centGens ++ yCands.map Prod.snd
meta def wTabs : Array (Array Nat) := gensOf wListM

meta def genZ : Array (Array Nat) := gensOf oGensZ
meta def genAZ : Array (Array Nat) := gensOf oGensAZ
meta def genY0 : Array (Array Nat) := gensOf (ykWords.getD 0 [])
meta def genY1 : Array (Array Nat) := gensOf (ykWords.getD 1 [])
meta def ids6 : Array (Array Nat) := Array.replicate 6 idM
meta def ids2 : Array (Array Nat) := Array.replicate 2 idM

meta def recZ : Array (Array Nat) := recOf genZ
meta def recAZ : Array (Array Nat) := recOf genAZ
meta def recY0 : Array (Array Nat) := recOf genY0
meta def recY1 : Array (Array Nat) := recOf genY1

meta def oneOrM (t q : Array Nat) : Bool := q == idM || q == t
meta def sqM (y : Array Nat) : Array Nat := mulM y y
meta def p5M (y : Array Nat) : Array Nat := let y2 := mulM y y; mulM (mulM y2 y2) y

meta def filtIdx (R : Array (Array Nat)) (t s : Array Nat) (pw : Array Nat → Array Nat) :
    Array Nat :=
  (List.range R.size).toArray.filter fun i => oneOrM t (pw (mulM s R[i]!))

meta def posRows (n : Nat) (I : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for a in [0:I.size] do
    r := r.set! I[a]! a
  return r

meta def u4M (y₁ y₂ : Array Nat) : Array Nat := let u := mulM y₁ y₂; let u2 := mulM u u; mulM u2 u2

meta def codesOf (R : Array (Array Nat)) (kt : Nat) (A B : Array (Array Nat)) : Array Nat :=
  Id.run do
    let M := indexOf R
    let mut cs : Array Nat := #[]
    let mut g := 0
    for y₁ in A do
      for y₂ in B do
        match M[u4M y₁ y₂]? with
        | some k =>
          if k != 0 && k != kt then
            cs := cs.push k
          else
            cs := cs.push (1000 + g)
            g := g + 1
        | none =>
          cs := cs.push (1000 + g)
          g := g + 1
    return cs

meta def goodOf (A B : Array (Array Nat)) (cs : Array Nat) : Array (Array Nat × Array Nat) :=
  Id.run do
    let mut r := #[]
    for a in [0:A.size] do
      for b in [0:B.size] do
        if 1000 ≤ cs[a * B.size + b]! then
          r := r.push (A[a]!, B[b]!)
    return r

meta def ciOf (R G : Array (Array Nat)) (t s₁ s₂ : Array Nat) (cg : List (List Nat)) : Array Nat :=
  let M := indexOf R
  let f := fun x => M.getD x R.size
  #[f t, f (sqM s₁), f (p5M s₂)] ++
    ((cg.map wM).toArray.map fun c => G.map fun g => f (mulM (mulM c g) (invTab 1408 c))).flatten

meta def keyOf (z : Array Nat) : Array Nat := z.extract 0 12

meta def keyMap (R : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:R.size] do
    m := m.insert (keyOf R[i]!) i
  return m

meta def candT : Array (Array Nat) := (yCands.map fun p => wM p.2).toArray
meta def candI : Array (Array Nat) := candT.map (invTab 1408)
meta def yRecs : Array (Array (Array Nat)) := #[recY0, recY1]
meta def yKeys : Array (Std.HashMap (Array Nat) Nat) := yRecs.map keyMap

meta def conjKey (c ci y : Array Nat) : Array Nat :=
  (List.range 12).toArray.map fun i => c.getD (y.getD (ci.getD i 0) 0) 0

meta def findGood (y₁ y₂ : Array Nat) : Array Nat := Id.run do
  for ci in [0:candT.size] do
    let c := candT[ci]!
    let cinv := candI[ci]!
    for k in [0:2] do
      let m : Std.HashMap (Array Nat) Nat := yKeys[k]!
      let Y : Array (Array Nat) := yRecs[k]!
      match m.get? (conjKey c cinv y₁), m.get? (conjKey c cinv y₂) with
      | some j₁, some j₂ =>
        if mulM c y₁ == mulM Y[j₁]! c && mulM c y₂ == mulM Y[j₂]! c then
          return #[k, ci, j₁, j₂]
      | _, _ => pure ()
  return #[0, 0, 0, 0]

meta def actC (y : Array Nat) (e : Nat) : Nat := y[e / 1408]! * 1408 + y[e % 1408]!

meta def orbC (gs : Array (Array Nat)) (e₀ : Nat) : Array Nat × Array Nat := Id.run do
  let mut E : Array Nat := #[e₀]
  let mut PA : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert e₀
  for h in [0:2000000] do
    if h < E.size then
      for l in [0:gs.size] do
        let x := actC gs[l]! E[h]!
        if !seen.contains x then
          seen := seen.insert x
          E := E.push x
          PA := PA.push (h + 16777216 * l)
    else break
  return (E, PA)

meta def baseOf (gs : Array (Array Nat)) : Nat := Id.run do
  for p in [0:1408] do
    let s := (orbC gs (p * 1408 + p)).1.size
    if s == 240 then return p * 1408 + p
    if s == 120 then
      for q in [0:1408] do
        if (orbC gs (p * 1408 + q)).1.size == 240 then return p * 1408 + q
  return 0

meta def orbData (y₁ y₂ : Array Nat) : Array (Array Nat) :=
  let gs := #[y₁, y₂]
  let (E, PA) := orbC gs (baseOf gs)
  let N := E.size
  let pos : Std.HashMap Nat Nat := Id.run do
    let mut m : Std.HashMap Nat Nat := {}
    for i in [0:N] do
      m := m.insert E[i]! i
    return m
  let SG := (List.range N).toArray.qsort fun a b => E[a]! < E[b]!
  let CT := ((List.range N).toArray.map fun k =>
    gs.map fun g => pos.getD (actC g E[k]!) N).flatten
  #[E, PA, SG, CT]

meta def tZ : Array Nat := wTabs[2]!
meta def tAZ : Array Nat := wTabs[3]!
meta def s1M : Array Nat := wTabs[0]!
meta def s2M : Array Nat := wTabs[1]!

meta def iAz : Array Nat := filtIdx recZ tZ s1M sqM
meta def iBz : Array Nat := filtIdx recZ tZ s2M p5M
meta def yaZ : Array (Array Nat) := iAz.map fun i => mulM s1M recZ[i]!
meta def ybZ : Array (Array Nat) := iBz.map fun i => mulM s2M recZ[i]!
meta def faZ : Array Nat := posRows 128 iAz
meta def fbZ : Array Nat := posRows 128 iBz
meta def ciZ : Array Nat := ciOf recZ genZ tZ s1M s2M classz.centGens
meta def cZ : Array Nat := codesOf recZ ciZ[0]! yaZ ybZ

meta def iAaz : Array Nat := filtIdx recAZ tAZ s1M sqM
meta def iBaz : Array Nat := filtIdx recAZ tAZ s2M p5M
meta def yaAZ : Array (Array Nat) := iAaz.map fun i => mulM s1M recAZ[i]!
meta def ybAZ : Array (Array Nat) := iBaz.map fun i => mulM s2M recAZ[i]!
meta def faAZ : Array Nat := posRows 128 iAaz
meta def fbAZ : Array Nat := posRows 128 iBaz
meta def ciAZ : Array Nat := ciOf recAZ genAZ tAZ s1M s2M classaz.centGens
meta def cAZ : Array Nat := codesOf recAZ ciAZ[0]! yaAZ ybAZ

meta def goodAZ : Array (Array Nat × Array Nat) := goodOf yaAZ ybAZ cAZ
meta def gInfo : Array (Array Nat) := goodAZ.map fun p => findGood p.1 p.2
meta def gK : Array Nat := gInfo.map (·[0]!)
meta def gC : Array Nat := gInfo.map (·[1]!)
meta def gJ : Array Nat := (gInfo.map fun r => #[r[2]!, r[3]!]).flatten
meta def gOrb : Array (Array (Array Nat)) := goodAZ.map fun p => orbData p.1 p.2
meta def oE : Array Nat := (gOrb.map (·[0]!)).flatten
meta def oPA : Array Nat := (gOrb.map (·[1]!)).flatten
meta def oSG : Array Nat := (gOrb.map (·[2]!)).flatten
meta def oCT : Array Nat := (gOrb.map (·[3]!)).flatten

end CFSG.KD.HN1408.Y442202M

open CFSG.KD.HN1408.Y442202M in
#kmulh CFSG.KD.HN1408.Y442202.OZ 1408 11 genZ ids6 idM 4096
open CFSG.KD.HN1408.Y442202M in
#kmulh CFSG.KD.HN1408.Y442202.OAZ 1408 11 genAZ ids6 idM 4096
open CFSG.KD.HN1408.Y442202M in
#kmulh CFSG.KD.HN1408.Y442202.Y0 1408 11 genY0 ids2 idM 4096
open CFSG.KD.HN1408.Y442202M in
#kmulh CFSG.KD.HN1408.Y442202.Y1 1408 11 genY1 ids2 idM 4096
open CFSG.KD.HN1408.Y442202M in
#kmisc_packarrs CFSG.KD.HN1408.Y442202.W wTabs 11
open CFSG.KD.HN1408.Y442202M in
#kmisc_packarrs CFSG.KD.HN1408.Y442202.YAz yaZ 11
open CFSG.KD.HN1408.Y442202M in
#kmisc_packarrs CFSG.KD.HN1408.Y442202.YBz ybZ 11
open CFSG.KD.HN1408.Y442202M in
#kmisc_packarrs CFSG.KD.HN1408.Y442202.YAaz yaAZ 11
open CFSG.KD.HN1408.Y442202M in
#kmisc_packarrs CFSG.KD.HN1408.Y442202.YBaz ybAZ 11
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.FAz faZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.FBz fbZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.CIz ciZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.Cz cZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.FAaz faAZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.FBaz fbAZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.CIaz ciAZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.Caz cAZ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.GK gK
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.GC gC
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.GJ gJ
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.OE oE
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.OPA oPA
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.OSG oSG
open CFSG.KD.HN1408.Y442202M in
#krows32 CFSG.KD.HN1408.Y442202.OCT oCT

public section

namespace CFSG.KD.HN1408.Y442202

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5

@[expose] def wList : List (List Nat) :=
  [sOne, sTwo, classz.rep, classaz.rep] ++ classz.centGens ++ classaz.centGens ++ yCands.map Prod.snd

end CFSG.KD.HN1408.Y442202

end
