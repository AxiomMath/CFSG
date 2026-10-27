module

public import Certificates.Kernel.LocalComp.BfsGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Certificates.Data.TwinPerpSmSp1Wit
public meta import Lean
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

open Lean Elab Command

public section

namespace CFSG.KC.Q8WitGen

open CFSG.KC.Tab CFSG.KS.RawGen
open CFSG.Monster.B.Co2.Native (compA eqA invCand idA)

meta def diffPt (n : Nat) (a b : Array Nat) : Nat :=
  ((List.range n).find? fun p => a[p]! != b[p]!).getD n

meta def q8E (n : Nat) (x y : Array Nat) (j : Nat) : Array Nat :=
  Certificates.TwinPerpSmSp1.q8Elt n x y j

elab "#q8wp_data " pre:ident dId:ident ww:num : command => do
  let P := pre.getId
  let w := ww.getNat
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let D ← liftTermElabM <| unsafe evalConst Certificates.TwinPerpSmSp1.Q8WitData dN
  let n := D.syl.n
  let gens := CFSG.CGT.PushingUpLit.SolKNA.R4.Check.qGens D.syl
  let (pts, _) := CFSG.KC.BfsGen.search n w gens
  let cs := Certificates.TwinPerpSmSp1.cands D
  let id := idA n
  let sq := pts.map fun a => compA n a a
  let sqP := sq.map (pack w)
  let mut rows : Array Nat := #[]
  let mut rk : Array Nat := #[]
  let mut rf : Array Nat := #[]
  let mut ro : Array Nat := #[]
  let mut rn : Array Nat := #[]
  for i in [0:pts.size] do
    let x := pts[i]!
    let s := sq[i]!
    let xi := invCand n x
    let mut row := 0
    if !(eqA n s id) && eqA n (compA n s s) id then
      for j in [0:pts.size] do
        if sqP[j]! == sqP[i]! then
          let y := pts[j]!
          let l := compA n y x
          let r := compA n xi y
          let v := if eqA n l r then 8193 + rk.size else diffPt n l r + 1
          if eqA n l r then
            let ks := (List.range cs.size).filter fun k =>
              Certificates.TwinPerpSmSp1.wit4 n x y cs[k]!
            let k := ks.headD 0
            let c := cs[k]!
            let ci := invCand n c
            let fx := Certificates.TwinPerpSmSp1.outsideA n x y c x
            let a := if fx then x else y
            let ca := compA n c a
            let pp := (List.range 8).foldr (fun j8 acc =>
              acc * 8192 + diffPt n ca (compA n (q8E n x y j8) c)) 0
            let opts := [(x, x), (x, y), (y, x), (y, y)]
            let o := ((List.range 4).find? fun t =>
              let (a', u) := opts[t]!
              let b := compA n (compA n c u) ci
              !(eqA n (compA n a' b) (compA n b a'))).getD 0
            let (a', u) := opts[o]!
            let b := compA n (compA n c u) ci
            let np := diffPt n (compA n a' b) (compA n b a')
            rk := rk.push k
            rf := rf.push (if fx then 1 else 0)
            ro := ro.push pp
            rn := rn.push (8192 * o + np)
          row := row ||| (v <<< (14 * j))
    rows := rows.push row
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `SQ) sqP
    addTree (P ++ `I) (pts.map fun a => pack w (invCand n a))
    addTree (P ++ `C) (cs.map (pack w))
    addTree (P ++ `CI) (cs.map fun a => pack w (invCand n a))
    addDef (P ++ `nc) natT (lit cs.size)
    addTree (P ++ `R) rows
    addTree (P ++ `RK) rk
    addTree (P ++ `RF) rf
    addTree (P ++ `RO) ro
    addTree (P ++ `RN) rn

end CFSG.KC.Q8WitGen

end
