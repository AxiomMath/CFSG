module

public import Certificates.Kernel.HN1023016.DataCl
public meta import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.HN1023016.Ev

open CFSG.KC.Eval CFSG.KC.LQT.Cmd

meta def natV (v : Val) : Except String Nat :=
  match v with
  | .nat n => pure n
  | _ => throw "expected a number"

meta def listV (v : Val) : Except String (Array Val) :=
  match v with
  | .list xs => pure xs
  | _ => throw "expected a list"

meta def natsV (v : Val) : Except String (Array Nat) := do
  (← listV v).mapM natV

meta def pairsV (v : Val) : Except String (Array (Nat × Nat)) := do
  (← listV v).mapM fun p => do
    let q ← natsV p
    if q.size != 2 then throw "expected a pair"
    pure (q[0]!, q[1]!)

meta def lkIdx (n r : Nat) : Option Nat :=
  if r >>> 6 == n >>> 6 then
    let i := n - 1 - r
    if i < n % 64 then some (n - 1 - i) else none
  else
    let bi := (n >>> 6) - (r >>> 6) - 1
    if bi < n / 64 then some (64 * (n / 64 - 1 - bi) + (r &&& 63)) else none

meta def runRegs (c : LayV) (R : Array Nat) (ops : Array (Nat × Nat)) : Array Nat := Id.run do
  let mut R := R
  for (a, b) in ops do
    let n := R.size
    let x := c.mul ((lkIdx n a).elim c.ONE (R[·]!)) ((lkIdx n b).elim c.ONE (R[·]!))
    R := R.push x
  return R

meta def storeOut (vals : Array Nat) (n0 : Nat) (refs : Array Val) (nm bn : Nat → Lean.Name)
    (vr bl : Lean.Name) : Array (Lean.Name × Val) := Id.run do
  let mut out : Array (Lean.Name × Val) := #[]
  let mut rv : Array Val := refs
  for r in [n0:vals.size] do
    out := out.push (nm r, .nat vals[r]!)
    rv := rv.push (.ref (nm r))
  let J := vals.size / 64
  for j in [0:J] do
    out := out.push (bn j, .list ((List.range 64).reverse.map fun t => rv[64 * j + t]!).toArray)
  out := out.push (vr, .list rv.reverse)
  out := out.push (bl, .list (if J = 0 then #[.list #[]] else
    ((List.range J).reverse.map fun j => Val.ref (bn j)).toArray))
  return out

meta def run (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 9 then throw "run: expected 9 arguments"
  let prg ← pairsV args[0]!
  let px ← pairsV args[1]!
  let A ← natV args[2]!
  let B ← natV args[3]!
  let ONE ← natV args[4]!
  let wg ← natsV args[5]!
  let hw ← (← listV args[6]!).mapM natsV
  let ce ← (← listV args[7]!).mapM fun c => do (← listV c).mapM natsV
  let lp ← (← listV args[8]!).mapM pairsV
  let c := layOf 5 133
  if c.ONE != ONE then throw "run: ONE is not the identity of the layout"
  let R := runRegs c #[ONE, A, B] (prg ++ px)
  let N := R.size
  let reg (r : Nat) : Nat := (lkIdx N r).elim ONE (R[·]!)
  let regRef (r : Nat) : Val := (lkIdx N r).elim (.ref `one) fun i => .ref (Lean.Name.mkSimple s!"v{i}")
  let mut out : Array (Lean.Name × Val) := #[(`one, .nat ONE)]
  out := out ++ storeOut R 0 #[] (fun r => .mkSimple s!"v{r}") (fun j => .mkSimple s!"b{j}") `VR `BL
  let mut hs : Array Nat := #[]
  for i in [0:hw.size] do
    let mut acc := ONE
    for l in hw[i]! do
      acc := c.mul acc (reg (wg.getD l 0))
    hs := hs.push acc
    out := out.push (.mkSimple s!"h{i}", .nat acc)
  out := out.push (`HS, .list ((List.range hs.size).map fun i => Val.ref (.mkSimple s!"h{i}")).toArray)
  let mut pw : Array Val := #[]
  for i in [0:hs.size] do
    let h := hs[i]!
    let mut x := h
    let mut row : Array Val := #[.ref `one, .ref (.mkSimple s!"h{i}")]
    for e in [2:6] do
      x := c.mul x h
      out := out.push (.mkSimple s!"p{i}_{e}", .nat x)
      row := row.push (.ref (.mkSimple s!"p{i}_{e}"))
    pw := pw.push (.list row)
  out := out.push (`PW, .list pw)
  let mut cv : Array Val := #[]
  let mut cb : Array Val := #[]
  let mut cn : Array Val := #[]
  for k in [0:ce.size] do
    let zs := ce[k]!.foldl (fun acc e => acc ++ e.extract 7 e.size) #[]
    let lv : Array Nat := #[ONE] ++ hs ++ zs.map reg
    let lr : Array Val := #[.ref `one] ++ ((List.range hs.size).map fun i =>
      Val.ref (.mkSimple s!"h{i}")).toArray ++ zs.map regRef
    if 64 ≤ lv.size then throw s!"run: class {k} has {lv.size} letters"
    let CR := runRegs c lv (lp.getD k #[])
    out := out ++ storeOut CR lv.size lr (fun r => .mkSimple s!"c{k}_{r}")
      (fun j => .mkSimple s!"cb{k}_{j}") (.mkSimple s!"CV{k}") (.mkSimple s!"CB{k}")
    cv := cv.push (.ref (.mkSimple s!"CV{k}"))
    cb := cb.push (.ref (.mkSimple s!"CB{k}"))
    cn := cn.push (.nat lv.size)
  out := out.push (`CVL, .list cv)
  out := out.push (`CBL, .list cb)
  out := out.push (`CN, .list cn)
  return out

end CFSG.KD.HN1023016.Ev

#kc_repo #kc_json CFSG.KD.HN1023016.J "Certificates/Kernel/HN1023016/data/checks.json" 128672 6979095422913678635
    (prg : List (List Nat))

#kc_repo #kc_json CFSG.KD.HN1023016.J "Certificates/Kernel/HN1023016/data/m5.json" 7158 8951341654334376733
    (px : List (List Nat)) (lp : List (List (List Nat)))

#kc_eval CFSG.KD.HN1023016 S CFSG.KD.HN1023016.Ev.run J.prg J.px CFSG.KD.FamHNSeed.W1
  CFSG.KD.FamHNSeed.W2 CFSG.KD.FamHNSeed.ONE wg hw ce J.lp
