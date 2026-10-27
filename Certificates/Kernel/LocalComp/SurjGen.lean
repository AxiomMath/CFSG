module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KC.SurjGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

meta def packR (d : Nat) (R : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:R.size] do
    acc := acc ||| (R[i]! <<< (d * i))
  return acc

meta def invRows (d : Nat) (M : Array Nat) : Array Nat := Id.run do
  let mut L := M
  let mut R := Array.ofFn (n := d) fun i => 1 <<< i.val
  for c in [0:d] do
    let mut p := c
    while p < d && !(L[p]!.testBit c) do
      p := p + 1
    if p < d then
      let tl := L[c]!
      let tr := R[c]!
      L := (L.set! c L[p]!).set! p tl
      R := (R.set! c R[p]!).set! p tr
      for i in [0:d] do
        if i != c && L[i]!.testBit c then
          L := L.set! i (L[i]! ^^^ L[c]!)
          R := R.set! i (R[i]! ^^^ R[c]!)
  return R

meta def wordRows (d : Nat) (F : Int → Array Nat) (w : List Int) : Array Nat :=
  w.foldr (fun z acc => mulRows d (F z) acc) (idRows d)

meta def natListE (l : List Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

elab "#lc_surj " pre:ident dId:ident iId:ident : command => do
  let P := pre.getId
  let Df ← liftTermElabM <| unsafe evalConst (Unit → VecData)
    (← liftCoreM <| realizeGlobalConstNoOverload dId)
  let D := Df ()
  let I ← liftTermElabM <| unsafe evalConst (Array (List Int))
    (← liftCoreM <| realizeGlobalConstNoOverload iId)
  let d := D.d
  let rA := D.rowsA
  let rB := D.rowsB
  let rAI := invRows d rA
  let rBI := invRows d rB
  let base : Int → Array Nat := fun z =>
    if z = 0 then rA else if z = 1 then rAI else if z = 2 then rB else rBI
  let ims := I.map (wordRows d base)
  let imsI := ims.map (invRows d)
  let O := D.orbit ()
  let n := D.n
  let pts := O.pts
  let mut pos : Std.HashMap Nat Nat := {}
  for i in [0:pts.size] do
    pos := pos.insert pts[i]! i
  let mut PA := Array.replicate n 0
  let mut LB := Array.replicate n 0
  let mut seen := Array.replicate n false
  seen := seen.set! 0 true
  for h in [0:n] do
    let a := ap O.alpha h
    if !seen[a]! then
      seen := seen.set! a true
      PA := PA.set! a h
      LB := LB.set! a 0
    let b := ap O.beta h
    if !seen[b]! then
      seen := seen.set! b true
      PA := PA.set! b h
      LB := LB.set! b 1
  let AP := (Array.range n).map fun h => ap O.alpha h
  let BP := (Array.range n).map fun h => ap O.beta h
  let SO := (Array.range n).qsort fun a b => pts[a]! < pts[b]!
  let mut SOI := Array.replicate n 0
  for m in [0:n] do
    SOI := SOI.set! SO[m]! m
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `A) natT (lit (packR d rA))
    addDef (P ++ `B) natT (lit (packR d rB))
    addDef (P ++ `AI) natT (lit (packR d rAI))
    addDef (P ++ `BI) natT (lit (packR d rBI))
    addDef (P ++ `Ims) (mkApp (mkConst ``List [0]) natT) (natListE (ims.map (packR d)).toList)
    addDef (P ++ `ImsI) (mkApp (mkConst ``List [0]) natT) (natListE (imsI.map (packR d)).toList)
    addTree (P ++ `PT) (pts.extract 0 n)
    addTree (P ++ `PA) PA
    addTree (P ++ `LB) LB
    addTree (P ++ `AP) AP
    addTree (P ++ `BP) BP
    addTree (P ++ `SO) SO
    addTree (P ++ `SOI) SOI

elab "#lc_words " pre:ident sId:ident : command => do
  let P := pre.getId
  let s ← liftTermElabM <| unsafe evalConst String
    (← liftCoreM <| realizeGlobalConstNoOverload sId)
  let W := (CFSG.Sporadic.Bridge.SurjD.Native.parseWords s).toList
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `W) (toTypeExpr (List (List Int))) (toExpr W)

end CFSG.KC.SurjGen

end
