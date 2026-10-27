module

public meta import Lean
meta import Certificates.Data.G2ThreeMaxCheck
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace CFSG.KD.G2Three.PrimGen

open Certificates.G2ThreeMax

meta def bitsM (v : Nat) (l : List Nat) : Nat :=
  l.foldr (fun e acc => 2 * acc + if e == v then 1 else 0) 0

meta def pkM (m : List Nat) : Nat := 2 ^ 196 * bitsM 2 m + bitsM 1 m

meta def LOm : Nat := 2 ^ 196 - 1
meta def RMm : Nat := 2 ^ 14 - 1
meta def CIm : Nat := (List.range 14).foldl (fun a i => a ||| (1 <<< (14 * i))) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let A1 := A &&& LOm
  let A2 := A >>> 196
  let B1 := B &&& LOm
  let B2 := B >>> 196
  let mut x1 := 0
  let mut x2 := 0
  for k in [0:14] do
    let a1 := (A1 >>> k) &&& CIm
    let a2 := (A2 >>> k) &&& CIm
    let b1 := (B1 >>> (14 * k)) &&& RMm
    let b2 := (B2 >>> (14 * k)) &&& RMm
    let q := a1 * b1 + a2 * b2
    let m := a1 * b2 + a2 * b1
    let t := (x1 ||| m) ^^^ (x2 ||| q)
    let z1 := (x2 ||| m) ^^^ t
    let z2 := (x1 ||| q) ^^^ t
    x1 := z1
    x2 := z2
  return x1 + (x2 <<< 196)

meta def oneM : Nat := pkM idArr.toList

meta def gK : Array Nat := (List.range 8).toArray.map fun k => pkM (genArr k).toList

meta def inv8M (k : Nat) : Nat := if k % 2 == 0 then k + 1 else k - 1

meta def wAM (w : List Nat) : Nat := w.foldr (fun k acc => mulM gK[k]! acc) oneM

meta def wBM (σ : List Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc k => mulM gK[inv8M σ[k]!]! acc) oneM

meta def actM (A B P : Nat) : Nat := mulM (mulM A P) B

structure Recs where
  X : List Nat
  IMG : List Nat
  LAB : List Nat
  HP : List Nat
  HS : List Nat
  HA : List Nat
  HB : List Nat
  ROOTS : List Nat
  RL : List Nat
  RC : List Nat
  RA : List Nat
  RB : List Nat
  TP : List Nat
  TD : List Nat
  EU : List Nat
  EV : List Nat
  CA : List Nat
  CB : List Nat
  m : Nat

meta def build (inp : Input) : Recs := Id.run do
  let σ := inp.sigma
  let ca := [0, 2, 4, 6].toArray.map fun l => gK[l]!
  let cb := [0, 2, 4, 6].toArray.map fun l => gK[inv8M σ[l]!]!
  let root := wAM inp.base
  let mut pts : Array Nat := #[root]
  let mut par : Array (Nat × Nat) := #[(0, 0)]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert root 0
  let mut h := 0
  while h < pts.size do
    for k in [0:4] do
      let y := actM ca[k]! cb[k]! pts[h]!
      if !idx.contains y then
        idx := idx.insert y pts.size
        pts := pts.push y
        par := par.push (h, 2 * k)
    h := h + 1
  let N := pts.size
  let ha := inp.stab.toArray.map wAM
  let hb := inp.stab.toArray.map (wBM σ)
  let mut newIdx : Array Nat := Array.replicate N 0
  let mut seen : Array Bool := Array.replicate N false
  let mut ord : Array Nat := #[]
  let mut lab : Array Nat := #[]
  let mut hp : Array Nat := #[]
  let mut hs : Array Nat := #[]
  let mut roots : Array Nat := #[]
  let mut rootOld : Array Nat := #[]
  for o in [0:N] do
    if !seen[o]! then
      let p := roots.size
      roots := roots.push ord.size
      rootOld := rootOld.push o
      seen := seen.set! o true
      newIdx := newIdx.set! o ord.size
      ord := ord.push o
      lab := lab.push p
      hp := hp.push 0
      hs := hs.push 0
      let mut q := ord.size - 1
      while q < ord.size do
        let u := ord[q]!
        for s in [0:ha.size] do
          let v := idx.getD (actM ha[s]! hb[s]! pts[u]!) 0
          if !seen[v]! then
            seen := seen.set! v true
            newIdx := newIdx.set! v ord.size
            ord := ord.push v
            lab := lab.push p
            hp := hp.push q
            hs := hs.push s
        q := q + 1
  let m := roots.size
  let X := ord.map fun o => pts[o]!
  let img := (List.range N).toArray.flatMap fun i =>
    (List.range 4).toArray.map fun k => newIdx[idx.getD (actM ca[k]! cb[k]! X[i]!) 0]!
  let wordOf (o : Nat) : List Nat := Id.run do
    let mut w : List Nat := []
    let mut c := o
    while c != 0 do
      w := w ++ [par[c]!.2]
      c := par[c]!.1
    return w
  let ws := rootOld.map wordOf
  let rl := ws.map (·.length)
  let rc := ws.map fun w => w.foldr (fun k acc => k + 8 * acc) 0
  let ra := ws.map wAM
  let rb := ws.map (wBM σ)
  let mut mem : Array (Array Nat) := Array.replicate m #[]
  for i in [0:N] do
    mem := mem.modify lab[i]! (·.push i)
  let mut tp : Array Nat := Array.replicate (m * m) 0
  let mut td : Array Nat := Array.replicate (m * m) 0
  let mut eu : Array Nat := Array.replicate (m * m) 0
  let mut ev : Array Nat := Array.replicate (m * m) 0
  for j in [1:m] do
    let mut vis : Array Bool := (Array.replicate m false).set! 0 true
    let mut queue : Array Nat := #[0]
    let mut qi := 0
    while qi < queue.size && queue.size < m do
      let q := queue[qi]!
      for i in mem[q]! do
        if queue.size == m then break
        let v := newIdx[idx.getD (actM ra[j]! rb[j]! X[i]!) 0]!
        let q' := lab[v]!
        if !vis[q']! then
          vis := vis.set! q' true
          queue := queue.push q'
          tp := tp.set! (j * m + q') q
          td := td.set! (j * m + q') (td[j * m + q]! + 1)
          eu := eu.set! (j * m + q') i
          ev := ev.set! (j * m + q') v
      qi := qi + 1
  return Recs.mk X.toList img.toList lab.toList hp.toList hs.toList ha.toList hb.toList
    roots.toList rl.toList rc.toList ra.toList rb.toList tp.toList td.toList eu.toList ev.toList
    ca.toList cb.toList m

meta def rI : Recs := build innerInput
meta def rO : Recs := build outerInput

meta def xI : List Nat := rI.X
meta def imgI : List Nat := rI.IMG
meta def labI : List Nat := rI.LAB
meta def hpI : List Nat := rI.HP
meta def hsI : List Nat := rI.HS
meta def haI : List Nat := rI.HA
meta def hbI : List Nat := rI.HB
meta def rootsI : List Nat := rI.ROOTS
meta def rlI : List Nat := rI.RL
meta def rcI : List Nat := rI.RC
meta def raI : List Nat := rI.RA
meta def rbI : List Nat := rI.RB
meta def tpI : List Nat := rI.TP
meta def tdI : List Nat := rI.TD
meta def euI : List Nat := rI.EU
meta def evI : List Nat := rI.EV
meta def caI : List Nat := rI.CA
meta def cbI : List Nat := rI.CB

meta def xO : List Nat := rO.X
meta def imgO : List Nat := rO.IMG
meta def labO : List Nat := rO.LAB
meta def hpO : List Nat := rO.HP
meta def hsO : List Nat := rO.HS
meta def haO : List Nat := rO.HA
meta def hbO : List Nat := rO.HB
meta def rootsO : List Nat := rO.ROOTS
meta def rlO : List Nat := rO.RL
meta def rcO : List Nat := rO.RC
meta def raO : List Nat := rO.RA
meta def rbO : List Nat := rO.RB
meta def tpO : List Nat := rO.TP
meta def tdO : List Nat := rO.TD
meta def euO : List Nat := rO.EU
meta def evO : List Nat := rO.EV
meta def caO : List Nat := rO.CA
meta def cbO : List Nat := rO.CB

end CFSG.KD.G2Three.PrimGen


#kss_ntree CFSG.KD.G2Three.PIX CFSG.KD.G2Three.PrimGen.xI
#kss_ntree CFSG.KD.G2Three.PIIMG CFSG.KD.G2Three.PrimGen.imgI
#kss_ntree CFSG.KD.G2Three.PILAB CFSG.KD.G2Three.PrimGen.labI
#kss_ntree CFSG.KD.G2Three.PIHP CFSG.KD.G2Three.PrimGen.hpI
#kss_ntree CFSG.KD.G2Three.PIHS CFSG.KD.G2Three.PrimGen.hsI
#kss_ntree CFSG.KD.G2Three.PIHA CFSG.KD.G2Three.PrimGen.haI
#kss_ntree CFSG.KD.G2Three.PIHB CFSG.KD.G2Three.PrimGen.hbI
#kss_ntree CFSG.KD.G2Three.PIROOTS CFSG.KD.G2Three.PrimGen.rootsI
#kss_ntree CFSG.KD.G2Three.PIRL CFSG.KD.G2Three.PrimGen.rlI
#kss_ntree CFSG.KD.G2Three.PIRC CFSG.KD.G2Three.PrimGen.rcI
#kss_ntree CFSG.KD.G2Three.PIRA CFSG.KD.G2Three.PrimGen.raI
#kss_ntree CFSG.KD.G2Three.PIRB CFSG.KD.G2Three.PrimGen.rbI
#kss_ntree CFSG.KD.G2Three.PITP CFSG.KD.G2Three.PrimGen.tpI
#kss_ntree CFSG.KD.G2Three.PITD CFSG.KD.G2Three.PrimGen.tdI
#kss_ntree CFSG.KD.G2Three.PIEU CFSG.KD.G2Three.PrimGen.euI
#kss_ntree CFSG.KD.G2Three.PIEV CFSG.KD.G2Three.PrimGen.evI
#kss_ntree CFSG.KD.G2Three.PICA CFSG.KD.G2Three.PrimGen.caI
#kss_ntree CFSG.KD.G2Three.PICB CFSG.KD.G2Three.PrimGen.cbI

#kss_ntree CFSG.KD.G2Three.POX CFSG.KD.G2Three.PrimGen.xO
#kss_ntree CFSG.KD.G2Three.POIMG CFSG.KD.G2Three.PrimGen.imgO
#kss_ntree CFSG.KD.G2Three.POLAB CFSG.KD.G2Three.PrimGen.labO
#kss_ntree CFSG.KD.G2Three.POHP CFSG.KD.G2Three.PrimGen.hpO
#kss_ntree CFSG.KD.G2Three.POHS CFSG.KD.G2Three.PrimGen.hsO
#kss_ntree CFSG.KD.G2Three.POHA CFSG.KD.G2Three.PrimGen.haO
#kss_ntree CFSG.KD.G2Three.POHB CFSG.KD.G2Three.PrimGen.hbO
#kss_ntree CFSG.KD.G2Three.POROOTS CFSG.KD.G2Three.PrimGen.rootsO
#kss_ntree CFSG.KD.G2Three.PORL CFSG.KD.G2Three.PrimGen.rlO
#kss_ntree CFSG.KD.G2Three.PORC CFSG.KD.G2Three.PrimGen.rcO
#kss_ntree CFSG.KD.G2Three.PORA CFSG.KD.G2Three.PrimGen.raO
#kss_ntree CFSG.KD.G2Three.PORB CFSG.KD.G2Three.PrimGen.rbO
#kss_ntree CFSG.KD.G2Three.POTP CFSG.KD.G2Three.PrimGen.tpO
#kss_ntree CFSG.KD.G2Three.POTD CFSG.KD.G2Three.PrimGen.tdO
#kss_ntree CFSG.KD.G2Three.POEU CFSG.KD.G2Three.PrimGen.euO
#kss_ntree CFSG.KD.G2Three.POEV CFSG.KD.G2Three.PrimGen.evO
#kss_ntree CFSG.KD.G2Three.POCA CFSG.KD.G2Three.PrimGen.caO
#kss_ntree CFSG.KD.G2Three.POCB CFSG.KD.G2Three.PrimGen.cbO
