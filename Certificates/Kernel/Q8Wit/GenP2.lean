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

meta def diffPt2 (n : Nat) (a b : Array Nat) : Nat :=
  ((List.range n).find? fun p => a[p]! != b[p]!).getD n

elab "#q8wp2_data " pre:ident dId:ident ww:num : command => do
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
  let mut ds : Array Nat := #[]
  let mut rm : Array Nat := #[]
  let mut mk : Array Nat := #[]
  let mut mz : Array Nat := #[]
  for i in [0:pts.size] do
    let x := pts[i]!
    let s := sq[i]!
    let s2 := compA n s s
    let mut row := 0
    ds := ds.push (if !(eqA n s id) && !(eqA n s2 id) then diffPt2 n s2 id + 1 else 0)
    if !(eqA n s id) && eqA n s2 id then
      let i0 := ((List.range pts.size).find? fun t => sqP[t]! == sqP[i]!).getD i
      for j in [0:pts.size] do
        if sqP[j]! == sqP[i]! then
          let y := pts[j]!
          let xi := invCand n x
          let isQ := eqA n (compA n y x) (compA n xi y)
          let mut v := 0
          if isQ then
            let ks := (List.range cs.size).filter fun k =>
              Certificates.TwinPerpSmSp1.wit4 n x y cs[k]!
            let k := ks.headD 0
            let m := ((List.range mk.size).find? fun t => mk[t]! == k && mz[t]! == i0).getD
              mk.size
            if m == mk.size then
              mk := mk.push k
              mz := mz.push i0
            v := 8193 + rm.size
            rm := rm.push m
          else
            v := diffPt2 n (compA n x (compA n y x)) y + 1
          row := row ||| (v <<< (14 * j))
    rows := rows.push row
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `ID) natT (lit (pack w id))
    addTree (P ++ `D) ds
    addTree (P ++ `R) rows
    addTree (P ++ `RM) rm
    addTree (P ++ `MK) mk
    addTree (P ++ `MZ) mz
    addDef (P ++ `nm) natT (lit mk.size)

end CFSG.KC.Q8WitGen

end
