module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs
import CFSG.Open.LocalVocabulary

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbTGen

open CFSG.EvenSporadicStandard.HNRecog

meta def hexv (c : Char) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

meta def hexChars : Array Char := h1408Hex.toList.toArray

meta def gens : Array (Array Nat) :=
  (Array.range 7).map fun j => (Array.range 1408).map fun i =>
    let o := 3 * (1408 * j + i)
    256 * hexv hexChars[o]! + 16 * hexv hexChars[o + 1]! + hexv hexChars[o + 2]!

meta def comp (p q : Array Nat) : Array Nat := q.map fun x => p[x]!

meta def idT : Array Nat := Array.range 1408

meta def inv (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 1408 0
  for i in [0:1408] do
    r := r.set! p[i]! i
  return r

meta def wordT (w : List Nat) : Array Nat := w.foldl (fun acc l => comp acc gens[l - 1]!) idT

meta def us : Array (Array Nat) := (classb.centGens.map wordT).toArray

meta def orbit : Array (Option (Array Nat × Nat × Nat × Nat)) := Id.run do
  let mut info : Array (Option (Array Nat × Nat × Nat × Nat)) := (Array.replicate 1408 none).set! 0
    (some (idT, 0, 0, 0))
  let mut q : Array Nat := #[0]
  let mut h := 0
  while h < q.size do
    let x := q[h]!
    let (tx, _, _, dx) := info[x]!.get!
    for l in [0:2] do
      let y := (us[l]!)[x]!
      if info[y]!.isNone then
        info := info.set! y (some (comp us[l]! tx, x, l, dx + 1))
        q := q.push y
    h := h + 1
  return info

meta def pts : Array Nat := (Array.range 1408).filter fun x => orbit[x]!.isSome

meta def posOf : Array Nat := Id.run do
  let mut r := Array.replicate 1408 0
  for k in [0:pts.size] do
    r := r.set! pts[k]! k
  return r

meta def t0 : Array (Array Nat) := pts.map fun x => orbit[x]!.get!.1

meta def p0 : Array (Array Nat) := pts.map fun x =>
  let (_, px, l, d) := orbit[x]!.get!
  #[posOf[px]!, l, d]

meta def closure (gs : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut els : Array (Array Nat) := #[idT]
  let mut h := 0
  while h < els.size do
    let x := els[h]!
    for g in gs do
      let y := comp g x
      if !els.contains y then
        els := els.push y
    h := h + 1
  return els

meta def schreier : Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut gs : Array (Array Nat) := #[]
  let mut rows : Array (Array Nat) := #[]
  let mut grp : Array (Array Nat) := #[idT]
  for p in [0:pts.size] do
    for l in [0:2] do
      if grp.size < 120 then
        let q := posOf[(us[l]!)[pts[p]!]!]!
        let s := comp (inv t0[q]!) (comp us[l]! t0[p]!)
        if !grp.contains s then
          gs := gs.push s
          rows := rows.push #[p, q, l]
          grp := closure gs
  return (gs, rows)

meta def t1rec : Array (Array Nat) × Array (Array Nat) := Id.run do
  let gs := schreier.1
  let mut els : Array (Array Nat) := #[idT]
  let mut rows : Array (Array Nat) := #[#[0, 0]]
  let mut h := 0
  while h < els.size do
    let x := els[h]!
    for r in [0:gs.size] do
      let y := comp gs[r]! x
      if !els.contains y then
        els := els.push y
        rows := rows.push #[h, r]
    h := h + 1
  return (els, rows)

meta def sT : Array (Array Nat) := schreier.1
meta def sR : Array (Array Nat) := schreier.2
meta def t1 : Array (Array Nat) := t1rec.1
meta def p1 : Array (Array Nat) := t1rec.2

end CFSG.KD.HN1408.CbTGen

#kmisc_packarrs CFSG.KD.HN1408.CbT.G CFSG.KD.HN1408.CbTGen.us 11
#kmisc_packarrs CFSG.KD.HN1408.CbT.T0 CFSG.KD.HN1408.CbTGen.t0 11
#kmisc_packarrs CFSG.KD.HN1408.CbT.P0 CFSG.KD.HN1408.CbTGen.p0 16
#kmisc_packarrs CFSG.KD.HN1408.CbT.S CFSG.KD.HN1408.CbTGen.sT 11
#kmisc_packarrs CFSG.KD.HN1408.CbT.SR CFSG.KD.HN1408.CbTGen.sR 16
#kmisc_packarrs CFSG.KD.HN1408.CbT.T1 CFSG.KD.HN1408.CbTGen.t1 11
#kmisc_packarrs CFSG.KD.HN1408.CbT.P1 CFSG.KD.HN1408.CbTGen.p1 16
