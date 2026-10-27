module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check
meta import CFSG.Sporadic.Mathieu.M24
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Std.Data.HashMap
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

namespace CFSG.KD.M24Three

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24

meta def aM : Array Nat :=
  (List.range 24).toArray.map fun i =>
    if h : i < 24 then (CFSG.Sporadic.Mathieu.m24gA ⟨i, h⟩).val else 0
meta def bM : Array Nat :=
  (List.range 24).toArray.map fun i =>
    if h : i < 24 then (CFSG.Sporadic.Mathieu.m24gB ⟨i, h⟩).val else 0
meta def idM : Array Nat := (List.range 24).toArray
meta def mulM (p q : Array Nat) : Array Nat := q.map fun i => p[i]!
meta def invM (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 24 0
  for i in [0:24] do
    r := r.set! p[i]! i
  return r
meta def letM (l : Int) : Array Nat :=
  if l = 1 then aM else if l = -1 then invM aM else if l = 2 then bM else invM bM
meta def wordM (w : List Int) : Array Nat := w.foldl (fun g l => mulM g (letM l)) idM
meta def codeM (l : Int) : Nat := if l = 1 then 0 else if l = 2 then 1 else if l = -1 then 2 else 3

meta def hA1W : List Int :=
  [-1, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, -1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -1,
   -2, -1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1]
meta def hA2W : List Int :=
  [-2, 1, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -1, -2, -1, -2, -1, -2, 1, 2, 1,
   2, 1, 2, 2, 1, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -1, -2, -2, -1, 2, -1, 2, -1, 2, -1, -2,
   -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, -1, 2]
meta def hB1W : List Int :=
  [-1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2,
   2, 1, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, -1, 2, -1, 2]
meta def hB2W : List Int :=
  [-1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -1, -2, -1,
   -2, -1, 2, 1, 2, 1, 2, 1, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, -1, 2, -1, 2]

meta def elWords : Array (List Int) :=
  #[xW, x2W, s1W, s2W, ca1W, ca2W, cb1W, cb2W, hA1W, hA2W, hB1W, hB2W,
    ra0W, ra1W, ra2W, ha0W, ha1W, ha2W, rb0W, rb1W, rb2W, hb0W, hb1W, hb2W]
meta def elM : Array (Array Nat) := elWords.map wordM
meta def eiM : Array (Array Nat) := elM.map invM
meta def wlM : Array (Array Nat) := elWords.map fun w => (w.map codeM).toArray
meta def lnM : Array (Array Nat) := elWords.map fun w => #[w.length]

meta def genM : Array (Array Nat) := #[aM, bM, invM aM, invM bM]
meta def xM : Array Nat := elM[0]!
meta def x2M : Array Nat := elM[1]!
meta def hAM : Array (Array Nat) := #[elM[8]!, elM[9]!]
meta def hAiM : Array (Array Nat) := hAM.map invM
meta def hBM : Array (Array Nat) := #[elM[10]!, elM[11]!]
meta def hBiM : Array (Array Nat) := hBM.map invM
meta def ids2M : Array (Array Nat) := #[idM, idM]
meta def cAM : Array (Array Nat) := #[elM[4]!, elM[5]!]
meta def cBM : Array (Array Nat) := #[elM[6]!, elM[7]!]
meta def sM : Array (Array Nat) := #[elM[2]!, elM[3]!]
meta def siM : Array (Array Nat) := sM.map invM
meta def sRecM : Array (Array Nat) :=
  (CFSG.PSL3Four.Native.bfs (fun j t => CFSG.PSL3Four.Native.conjTab 24 idM sM[j]! t) 2 idM 100).tabs
meta def sClM : Array (Array Nat) :=
  (sRecM.map fun e => (sM ++ siM).map fun g => mulM e g).flatten

meta def winvM (w : List Int) : List Int := w.reverse.map fun l => -l

meta def travM (gs : Array (Array Nat)) (gw : Array (List Int)) (p : Nat) :
    Array (Option (List Int)) := Id.run do
  let mut tr : Array (Option (List Int)) := Array.replicate 24 none
  tr := tr.set! p (some [])
  let mut q : Array Nat := #[p]
  for i in [0:24] do
    if i < q.size then
      let u := q[i]!
      for j in [0:gs.size] do
        let r := (gs[j]!)[u]!
        if tr[r]!.isNone then
          tr := tr.set! r (some (gw[j]! ++ tr[u]!.getD []))
          q := q.push r
  return tr

meta def schM (gw : Array (List Int)) (p N : Nat) : Array (List Int) := Id.run do
  let gs := gw.map wordM
  let tr := travM gs gw p
  let mut cands : Array (List Int) := #[]
  for u in [0:24] do
    if let some wu := tr[u]! then
      for j in [0:gs.size] do
        let r := (gs[j]!)[u]!
        cands := cands.push (winvM (tr[r]!.getD []) ++ gw[j]! ++ wu)
  let sorted := cands.qsort fun a b => a.length < b.length
  let mut out : Array (List Int) := #[]
  let mut seen : Array (Array Nat) := #[]
  for s in sorted do
    let g := wordM s
    if g != idM && !(seen.contains g) && out.size < N then
      out := out.push s
      seen := seen.push g
  return out

meta def chainM (b0 b1 b2 : Nat) : Array (Array (Option (List Int))) :=
  let g0 : Array (List Int) := #[[1], [2]]
  let g1 := schM g0 b0 8
  let g2 := schM g1 b1 8
  #[travM (g0.map wordM) g0 b0, travM (g1.map wordM) g1 b1, travM (g2.map wordM) g2 b2]
meta def chAM : Array (Array (Option (List Int))) := chainM 0 3 5
meta def chBM : Array (Array (Option (List Int))) := chainM 0 17 13
meta def trTabs : Array (Array (Option (List Int))) := chAM ++ #[chBM[1]!, chBM[2]!]
meta def trWM : Array (Array Nat) :=
  (trTabs.map fun T => T.map fun o => ((o.getD []).map codeM).toArray).flatten
meta def trLM : Array (Array Nat) :=
  (trTabs.map fun T => T.map fun o => #[(o.getD []).length]).flatten

meta def recM (gs : Array (Array Nat)) : Array (Array Nat) :=
  (CFSG.PSL3Four.Native.bfs (fun j t => CFSG.PSL3Four.Native.conjTab 24 idM gs[j]! t) gs.size
    idM 2000).tabs
meta def powM (p : Array Nat) (k : Nat) : Array Nat := (List.range k).foldl (fun g _ => mulM g p) idM
meta def covM (gs reps : Array (Array Nat)) (qs : List Nat) : Array (Array Nat) :=
  let R := recM gs
  R.map fun y => Id.run do
    if y != idM && qs.any (fun q => powM y q == idM) then
      let mut res := #[0, 0]
      let mut found := false
      for k in [0:R.size] do
        if !found then
          for j in [0:reps.size] do
            if !found && mulM y R[k]! == mulM R[k]! reps[j]! then
              res := #[j, k]
              found := true
      return res
    else
      return #[0, 0]
meta def covAM : Array (Array Nat) := covM cAM #[elM[12]!, elM[13]!, elM[14]!] [2, 5]
meta def covBM : Array (Array Nat) := covM cBM #[elM[18]!, elM[19]!, elM[20]!] [2, 7]

meta def ballM (t : Array Nat) (cap : Nat) : Std.HashMap (Array Nat) (List Int) := Id.run do
  let mut m : Std.HashMap (Array Nat) (List Int) := ({} : Std.HashMap (Array Nat) (List Int)).insert t []
  let mut q : Array (Array Nat) := #[t]
  for i in [0:cap] do
    if i < q.size && m.size < cap then
      let y := q[i]!
      let w := m.getD y []
      for l in [1, 2, -1, -2] do
        let g := letM l
        let z := mulM g (mulM y (invM g))
        if !m.contains z then
          m := m.insert z (l :: w)
          q := q.push z
  return m
meta def ballAM : Std.HashMap (Array Nat) (List Int) := ballM xM 4000
meta def ballBM : Std.HashMap (Array Nat) (List Int) := ballM x2M 6000
meta def sylConjM (e : Array Nat) : List Int × Nat := Id.run do
  let fixd := ((List.range 24).filter fun i => e[i]! == i).length
  let (B, c) := if fixd == 6 then (ballAM, 0) else (ballBM, 1)
  let mut m : Std.HashMap (Array Nat) (List Int) := ({} : Std.HashMap (Array Nat) (List Int)).insert e []
  let mut q : Array (Array Nat) := #[e]
  for i in [0:6000] do
    if i < q.size then
      let y := q[i]!
      let w' := m.getD y []
      if let some w := B.get? y then
        return (winvM w ++ w', c)
      for l in [1, 2, -1, -2] do
        let g := letM l
        let z := mulM g (mulM y (invM g))
        if !m.contains z then
          m := m.insert z (l :: w')
          q := q.push z
  return ([], 2)
meta def sylCM : Array (List Int × Nat) :=
  sRecM.map fun e => if e == idM then ([], 0) else sylConjM e
meta def sylWM : Array (Array Nat) := sylCM.map fun p => (p.1.map codeM).toArray
meta def sylLM : Array (Array Nat) := sylCM.map fun p => #[p.1.length, p.2]

end CFSG.KD.M24Three

public section

open CFSG.KD.M24Three in
#kmulh CFSG.KD.M24Three.OA 24 5 hAM hAiM xM 2000
open CFSG.KD.M24Three in
#kmulh CFSG.KD.M24Three.OB 24 5 hBM hBiM x2M 2000
open CFSG.KD.M24Three in
#kmulh CFSG.KD.M24Three.CA 24 5 ids2M cAM idM 2000
open CFSG.KD.M24Three in
#kmulh CFSG.KD.M24Three.CB 24 5 ids2M cBM idM 2000
open CFSG.KD.M24Three in
#kmulh CFSG.KD.M24Three.S 24 5 ids2M sM idM 100
open CFSG.KD.M24Three in
#kfind CFSG.KD.M24Three.SCl sRecM sClM
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.SI siM 5
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.GN genM 5
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.EL elM 5
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.EI eiM 5
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.WL wlM 2
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.LN lnM 16
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.TW trWM 2
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.TL trLM 16
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.CvA covAM 16
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.CvB covBM 16
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.SW sylWM 2
open CFSG.KD.M24Three in
#kmisc_packarrs CFSG.KD.M24Three.SL sylLM 16
