module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23Check
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Std.Data.HashMap
meta import Mathlib
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

namespace CFSG.KD.M23Cent3

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23

meta def aM : Array Nat :=
  (List.range 23).toArray.map fun i => if h : i < 23 then (gA ⟨i, h⟩).val else 0
meta def bM : Array Nat :=
  (List.range 23).toArray.map fun i => if h : i < 23 then (gB ⟨i, h⟩).val else 0
meta def idM : Array Nat := (List.range 23).toArray
meta def mulM (p q : Array Nat) : Array Nat := q.map fun i => p[i]!
meta def invM (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 23 0
  for i in [0:23] do
    r := r.set! p[i]! i
  return r
meta def letM (l : Int) : Array Nat :=
  if l = 1 then aM else if l = -1 then invM aM else if l = 2 then bM else invM bM
meta def wordM (w : List Int) : Array Nat := w.foldl (fun g l => mulM g (letM l)) idM
meta def codeM (l : Int) : Nat := if l = 1 then 0 else if l = 2 then 1 else if l = -1 then 2 else 3

meta def invW : List Int := [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1]

meta def elWords : Array (List Int) :=
  #[xW, yW, c1W, c2W, r0W, r1W, r2W, h0W, h1W, h2W, invW]
meta def elM : Array (Array Nat) := elWords.map wordM
meta def eiM : Array (Array Nat) := elM.map invM
meta def wlM : Array (Array Nat) := elWords.map fun w => (w.map codeM).toArray
meta def lnM : Array (Array Nat) := elWords.map fun w => #[w.length]

meta def genM : Array (Array Nat) := #[aM, bM, invM aM, invM bM]
meta def xM : Array Nat := elM[0]!
meta def ids2M : Array (Array Nat) := #[idM, idM]
meta def cM : Array (Array Nat) := #[elM[2]!, elM[3]!]
meta def sM : Array (Array Nat) := #[elM[0]!, elM[1]!]
meta def siM : Array (Array Nat) := sM.map invM
meta def sRecM : Array (Array Nat) :=
  (CFSG.PSL3Four.Native.bfs (fun j t => CFSG.PSL3Four.Native.conjTab 23 idM sM[j]! t) 2 idM 100).tabs
meta def sClM : Array (Array Nat) :=
  (sRecM.map fun e => (sM ++ siM).map fun g => mulM e g).flatten

meta def winvM (w : List Int) : List Int := w.reverse.map fun l => -l

meta def travM (gs : Array (Array Nat)) (gw : Array (List Int)) (p : Nat) :
    Array (Option (List Int)) := Id.run do
  let mut tr : Array (Option (List Int)) := Array.replicate 23 none
  tr := tr.set! p (some [])
  let mut q : Array Nat := #[p]
  for i in [0:23] do
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
  for u in [0:23] do
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

meta def baseM : Array Nat := #[0, 1, 2, 10, 15]

meta def chainM : Array (Array (Option (List Int))) := Id.run do
  let mut gw : Array (List Int) := #[[1], [2]]
  let mut out : Array (Array (Option (List Int))) := #[]
  for l in [0:5] do
    out := out.push (travM (gw.map wordM) gw baseM[l]!)
    if l < 4 then
      gw := schM gw baseM[l]! 8
  return out

meta def ptsM : Array (Array Nat) :=
  chainM.map fun T => Id.run do
    let mut r : Array Nat := #[]
    for q in [0:23] do
      if T[q]!.isSome then r := r.push q
    return r ++ Array.replicate (23 - r.size) 0
meta def ptM : Array (Array Nat) := (ptsM.map fun P => P.map fun q => #[q]).flatten
meta def trWM : Array (Array Nat) :=
  ((List.range 5).toArray.map fun l => (ptsM[l]!).map fun q =>
    (((chainM[l]!)[q]!.getD []).map codeM).toArray).flatten
meta def trLM : Array (Array Nat) :=
  ((List.range 5).toArray.map fun l => (ptsM[l]!).map fun q =>
    #[((chainM[l]!)[q]!.getD []).length]).flatten

meta def recM (gs : Array (Array Nat)) : Array (Array Nat) :=
  (CFSG.PSL3Four.Native.bfs (fun j t => CFSG.PSL3Four.Native.conjTab 23 idM gs[j]! t) gs.size
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
meta def cvM : Array (Array Nat) := covM cM #[elM[4]!, elM[5]!, elM[6]!] [2, 5]

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
meta def ballXM : Std.HashMap (Array Nat) (List Int) := ballM xM 4000
meta def sylConjM (e : Array Nat) : List Int := Id.run do
  let mut m : Std.HashMap (Array Nat) (List Int) := ({} : Std.HashMap (Array Nat) (List Int)).insert e []
  let mut q : Array (Array Nat) := #[e]
  for i in [0:6000] do
    if i < q.size then
      let y := q[i]!
      let w' := m.getD y []
      if let some w := ballXM.get? y then
        return winvM w ++ w'
      for l in [1, 2, -1, -2] do
        let g := letM l
        let z := mulM g (mulM y (invM g))
        if !m.contains z then
          m := m.insert z (l :: w')
          q := q.push z
  return []
meta def sylCM : Array (List Int) := sRecM.map fun e => if e == idM then [] else sylConjM e
meta def sylWM : Array (Array Nat) := sylCM.map fun w => (w.map codeM).toArray
meta def sylLM : Array (Array Nat) := sylCM.map fun w => #[w.length]

end CFSG.KD.M23Cent3

public section

open CFSG.KD.M23Cent3 in
#kmulh CFSG.KD.M23Cent3.CE 23 5 ids2M cM idM 2000
open CFSG.KD.M23Cent3 in
#kmulh CFSG.KD.M23Cent3.S 23 5 ids2M sM idM 100
open CFSG.KD.M23Cent3 in
#kfind CFSG.KD.M23Cent3.SCl sRecM sClM
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.SI siM 5
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.GN genM 5
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.EL elM 5
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.EI eiM 5
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.WL wlM 2
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.LN lnM 16
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.PT ptM 16
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.TW trWM 2
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.TL trLM 16
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.Cv cvM 16
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.SW sylWM 2
open CFSG.KD.M23Cent3 in
#kmisc_packarrs CFSG.KD.M23Cent3.SL sylLM 16
