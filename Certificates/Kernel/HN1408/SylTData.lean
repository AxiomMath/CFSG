module

public import Certificates.Kernel.LocalQT.PEnumD
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
meta import CFSG.Open.Defs
import CFSG.Open.LocalVocabulary

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylTGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel

meta def hexv (c : Char) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

meta def hexChars : Array Char := h1408Hex.toList.toArray

meta def gens : Array (Array Nat) :=
  (Array.range 7).map fun j => (Array.range 1408).map fun i =>
    let o := 3 * (1408 * j + i)
    256 * hexv hexChars[o]! + 16 * hexv hexChars[o + 1]! + hexv hexChars[o + 2]!

meta def comp (p q : Array Nat) : Array Nat := q.map fun x => p[x]!

meta def idT : Array Nat := Array.range 1408

meta def wordT (w : List Nat) : Array Nat := w.foldl (fun acc l => comp acc gens[l - 1]!) idT

meta def key (t : Array Nat) : Nat := t[2]! * 1408 + t[0]!

meta def sg : Array (Array Nat) := (sWords.map wordT).toArray
meta def sgi : Array (Array Nat) := (sWords.map fun w => wordT w.reverse).toArray

meta def recS : Array (Array Nat) := Id.run do
  let mut tabs : Array (Array Nat) := #[idT]
  let mut seen : Array Bool := (Array.replicate (1408 * 1408) false).set! (key idT) true
  let mut h := 0
  while h < tabs.size do
    let t := tabs[h]!
    for j in [0:5] do
      let y := comp sg[j]! t
      if !seen[key y]! then
        seen := seen.set! (key y) true
        tabs := tabs.push y
    h := h + 1
  return tabs

meta def idxS : Array Nat := Id.run do
  let mut r := Array.replicate (1408 * 1408) 0
  for i in [0:recS.size] do
    r := r.set! (key recS[i]!) i
  return r

meta def ix (t : Array Nat) : Nat := idxS[key t]!

meta def piM : Array Nat :=
  ((Array.range 25).map fun r => ix (comp sg[r / 5]! sg[r % 5]!))

meta def commT (i j : Nat) : Array Nat := comp (comp (comp sg[i]! sg[j]!) sgi[i]!) sgi[j]!

meta def ciM : Array Nat := (Array.range 25).map fun r => ix (commT (r / 5) (r % 5))

meta def g1T : Array (Array Nat) := (tpPairs.map fun p => commT p.1 p.2).toArray

meta def g2T : Array (Array Nat) := g1T ++ (w0Extra.map wordT).toArray

meta def sub (gs : Array (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut els : Array (Array Nat) := #[idT]
  let mut rows : Array Nat := #[0]
  let mut pos : Array Nat := (Array.replicate (1408 * 1408) 0)
  let mut seen : Array Bool := (Array.replicate (1408 * 1408) false).set! (key idT) true
  let mut h := 0
  while h < els.size do
    let x := els[h]!
    for t in [0:gs.size] do
      let y := comp x gs[t]!
      if !seen[key y]! then
        seen := seen.set! (key y) true
        pos := pos.set! (key y) els.size
        els := els.push y
        rows := rows.push (16 * h + t)
    h := h + 1
  let cl := (els.map fun x => gs.map fun g => pos[key (comp x g)]!).flatten
  return (els, rows, cl)

meta def sub1 := sub g1T
meta def sub2 := sub g2T

meta def posIn (els : Array (Array Nat)) (t : Array Nat) : Nat :=
  (els.findIdx? (· == t)).getD els.size

meta def g1M : Array Nat := g1T.map ix
meta def g2M : Array Nat := g2T.map ix
meta def e1M : Array Nat := sub1.1.map ix
meta def pl1M : Array Nat := sub1.2.1
meta def c1M : Array Nat := sub1.2.2
meta def e2M : Array Nat := sub2.1.map ix
meta def pl2M : Array Nat := sub2.2.1
meta def c2M : Array Nat := sub2.2.2
meta def ncM : Array Nat := (Array.range 30).map fun r =>
  posIn sub1.1 (comp (comp sg[r / 6]! g1T[r % 6]!) sgi[r / 6]!)
meta def cpM : Array Nat := (Array.range 25).map fun r => posIn sub1.1 (commT (r / 5) (r % 5))
meta def tgM : Array Nat := (tGens.map fun w => ix (wordT w)).toArray

end CFSG.KD.HN1408.SylTGen

#krows32 CFSG.KD.HN1408.SylT.PI CFSG.KD.HN1408.SylTGen.piM
#krows32 CFSG.KD.HN1408.SylT.CI CFSG.KD.HN1408.SylTGen.ciM
#krows32 CFSG.KD.HN1408.SylT.G1 CFSG.KD.HN1408.SylTGen.g1M
#krows32 CFSG.KD.HN1408.SylT.E1 CFSG.KD.HN1408.SylTGen.e1M
#krows32 CFSG.KD.HN1408.SylT.PL1 CFSG.KD.HN1408.SylTGen.pl1M
#krows32 CFSG.KD.HN1408.SylT.C1 CFSG.KD.HN1408.SylTGen.c1M
#krows32 CFSG.KD.HN1408.SylT.G2 CFSG.KD.HN1408.SylTGen.g2M
#krows32 CFSG.KD.HN1408.SylT.E2 CFSG.KD.HN1408.SylTGen.e2M
#krows32 CFSG.KD.HN1408.SylT.PL2 CFSG.KD.HN1408.SylTGen.pl2M
#krows32 CFSG.KD.HN1408.SylT.C2 CFSG.KD.HN1408.SylTGen.c2M
#krows32 CFSG.KD.HN1408.SylT.NC CFSG.KD.HN1408.SylTGen.ncM
#krows32 CFSG.KD.HN1408.SylT.CP CFSG.KD.HN1408.SylTGen.cpM
#krows32 CFSG.KD.HN1408.SylT.TG CFSG.KD.HN1408.SylTGen.tgM
