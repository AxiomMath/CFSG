module

public meta import Lean
public meta import Std.Data.HashMap
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import Certificates.Kernel.SporSch.GenSetReplay
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.SporSchCnt

open CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native

meta def eltArr (n : Nat) (L : Array CFSG.Monster.B.Co2.Native.Level) (nf : List Nat) : Array Nat :=
  let wd := nfWord L nf.toArray
  Array.ofFn (n := n) fun i => evR wd i.val

meta def fixes (bs : List Nat) (f : Nat → Nat) : Bool := bs.all fun b => f b == b

meta def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | e + 1, x => f (iter f e x)

meta def natLists (j : Json) (k : String) : Except String (List (List Nat)) := do
  let a ← (← j.getObjVal? k).getArr?
  a.toList.mapM fun e => do (← e.getArr?).toList.mapM fun v => v.getNat?

meta def srchNat (L : Array CFSG.Monster.B.Co2.Native.Level) (bs : List Nat) (X Y : Array Nat) (k0 : Nat) : Nat := Id.run do
  let p := L[0]!.pts[k0]!
  let u := (L[0]!.trInv[k0]!)[Y[p]!]!
  let k1 := L[1]!.pos[u]!
  if k1 < L[1]!.pts.size then
    let mut s := 0
    for k2 in [0:L[2]!.pts.size] do
      for k3 in [0:L[3]!.pts.size] do
        let wd := nfWord L #[k0, k1, k2, k3]
        if bs.all fun b => evR wd X[b]! == Y[evR wd b]! then
          s := s + 1
    return s
  else
    return 0

meta def scanNat (L : Array CFSG.Monster.B.Co2.Native.Level) (bs : List Nat) (Z : Nat → Nat) (nf : Array Nat) : Nat :=
  let wd := nfWord L nf
  let f := fun b => evR wd (Z b)
  let g := fun b => Z (Z (evR wd (Z b)))
  if fixes bs (iter f 3) && !fixes bs f && fixes bs (iter g 9) && !fixes bs (iter g 3) then 1
  else 0

end CFSG.KS.SporSchCnt

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen CFSG.KS.SporSchCnt
  CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native in
elab "#kss_cntdata " pre:ident nn:num ww:num lvId:ident bsId:ident clId:ident jsId:ident
    bS:num bC:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let cn (s : Ident) := liftCoreM <| realizeGlobalConstNoOverload s
  let L ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) (← cn lvId)
  let bs ← liftTermElabM <| unsafe evalConst (List Nat) (← cn bsId)
  let cl ← liftTermElabM <| unsafe evalConst
    (List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat)) (← cn clId)
  let txt ← liftTermElabM <| unsafe evalConst String (← cn jsId)
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "#kss_cntdata: {e}"
  let lst := fun (k : String) => match natLists j k with
    | .ok l => pure l
    | .error e => throwError "#kss_cntdata: {k}: {e}"
  let reps ← lst "reps"
  let r2 ← lst "r2"
  let d2 ← lst "d2"
  let r3 ← lst "r3"
  let d3 ← lst "d3"
  let arr := eltArr n L
  let nfN := fun (nf : List Nat) => pack 16 nf.toArray
  let T := arr reps[0]!
  let YA := arr reps[1]!
  let YB := arr reps[2]!
  let Z := arr reps[3]!
  let Z2 := comp n Z Z
  let r2a := r2.toArray.map arr
  let keyOf := fun (g : Array Nat) => imgKey n (bs.map fun b => g[b]!)
  let idx : Std.HashMap Nat Nat := (Array.range r2a.size).foldl (fun m i => m.insert (keyOf r2a[i]!) i) {}
  let m2 := Id.run do
    let mut out : Array Nat := #[]
    for i in [0:r2a.size] do
      for j in [0:r2a.size] do
        out := out.push (idx.getD (keyOf (comp n r2a[i]! r2a[j]!)) 255)
    return out
  let B := bS.getNat
  let nS := L[0]!.pts.size / B
  let vals := fun (X Y : Array Nat) => (Array.range nS).map fun g =>
    (List.range B).foldl (fun s j => s + srchNat L bs X Y (g * B + j)) 0
  let elts := cl[0]!.2.1
  let H := bC.getNat
  let nC := (elts.size + H - 1) / H
  let svals := fun (Zf : Nat → Nat) => (Array.range nC).map fun g =>
    (List.range H).foldl (fun s j =>
      if g * H + j < elts.size then s + scanNat L bs Zf elts[g * H + j]! else s) 0
  let nfRows := fun (l : List (List Nat)) => rows 64 (l.toArray.map fun nf => nfN nf)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `T) natT (lit (pack w T))
    addDef (P ++ `YA) natT (lit (pack w YA))
    addDef (P ++ `YB) natT (lit (pack w YB))
    addDef (P ++ `Z) natT (lit (pack w Z))
    addDef (P ++ `nT) natT (lit (nfN reps[0]!))
    addDef (P ++ `nYA) natT (lit (nfN reps[1]!))
    addDef (P ++ `nYB) natT (lit (nfN reps[2]!))
    addDef (P ++ `nZ) natT (lit (nfN reps[3]!))
    addDef (P ++ `nNu) natT (lit (nfN reps[4]!))
    addTree (P ++ `R2) (nfRows r2)
    addTree (P ++ `D2) (nfRows d2)
    addTree (P ++ `R3) (nfRows r3)
    addTree (P ++ `D3) (nfRows (d3.map fun e => e.drop 1))
    addTree (P ++ `C3) (rows 1 (d3.toArray.map fun e => e.headD 0))
    addTree (P ++ `M2) (rows 7 m2)
    addTree (P ++ `VT) (vals T T)
    addTree (P ++ `VA) (vals YA YA)
    addTree (P ++ `VB) (vals YB YB)
    addTree (P ++ `VZ) (vals Z Z)
    addTree (P ++ `VZ2) (vals Z Z2)
    addTree (P ++ `SZ) (svals fun b => Z[b]!)
    addTree (P ++ `SZ2) (svals fun b => Z2[b]!)
    addDef (P ++ `nS) natT (lit nS)
    addDef (P ++ `nC) natT (lit nC)

end
