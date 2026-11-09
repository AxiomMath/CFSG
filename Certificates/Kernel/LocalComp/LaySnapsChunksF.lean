module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnapsChunks
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Kernel.LocalComp.LaySnapsChunks

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.KC.LaySnapsChunks

public section

namespace CFSG.KC.LaySnapsChunksF

meta partial def splitN (S x cnt : Nat) (out : Array Nat) : Array Nat :=
  if cnt ≤ 8 then Id.run do
    let mut out := out
    let mut r := x
    let m := (1 <<< S) - 1
    for _ in [0:cnt] do
      out := out.push (r &&& m)
      r := r >>> S
    return out
  else
    let h := cnt / 2
    splitN S (x >>> (S * h)) (cnt - h) (splitN S (x &&& ((1 <<< (S * h)) - 1)) h out)

meta partial def joinN (S : Nat) (rows : Array Nat) (lo cnt : Nat) : Nat :=
  if cnt == 0 then 0
  else if cnt == 1 then rows[lo]!
  else
    let h := cnt / 2
    joinN S rows lo h ||| (joinN S rows (lo + h) (cnt - h) <<< (S * h))

meta def mulF (c : LayV) (A B : Nat) : Nat := Id.run do
  let ra := splitN c.S A c.d #[]
  let rb := splitN c.S B c.d #[]
  let m := (1 <<< c.w) - 1
  let mut rc : Array Nat := Array.mkEmpty c.d
  for i in [0:c.d] do
    let mut r := ra[i]!
    let mut acc := 0
    for k in [0:c.d] do
      if r == 0 then break
      let a := r &&& m
      r := r >>> c.w
      if a != 0 then acc := acc + a * rb[k]!
    rc := rc.push (c.red c.LV c.HV acc)
  return joinN c.S rc 0 c.d

meta def powF (c : LayV) (X e : Nat) : Nat := Id.run do
  let mut acc : Option Nat := none
  let mut b := X
  let mut k := e
  while 0 < k do
    if k % 2 == 1 then
      acc := some (match acc with
        | none => b
        | some a => mulF c a b)
    k := k / 2
    if 0 < k then b := mulF c b b
  return acc.getD c.ONE

meta def runChunkF (c : LayV) (pre : Name) (i : Nat) (one : Expr) (S : List (Nat × Expr)) (n : Nat)
    (ops : List (List Nat)) (out : List Nat) : CoreM (List (Nat × Expr)) := do
  let mut R : Array (Nat × Option Expr) :=
    (S.map (fun (p : Nat × Expr) => (p.1, some p.2)) ++
      List.replicate (n - S.length) (c.ONE, some one)).toArray
  let val (R : Array (Nat × Option Expr)) (i : Nat) : Nat := (R.getD i (c.ONE, none)).1
  for o in ops do
    match o with
    | [0, i, j, k] => R := R.set! k (mulF c (val R i) (val R j), none)
    | [e, i, _, k] => R := R.set! k (powF c (val R i) e, none)
    | _ => throwError "#lay_snaps_chunks_f: not an operation: {o}"
  let mut res := #[]
  for r in out do
    match R.getD r (c.ONE, some one) with
    | (x, some e) => res := res.push (x, e)
    | (x, none) =>
      let nm := pre ++ Name.mkSimple s!"S{i}_{res.size}"
      addDef nm natE (bigLit x)
      res := res.push (x, mkConst nm)
  return res.toList

elab "#lay_snaps_chunks_f " pre:ident p:num d:num a:ident b:ident cs:ident : command => do
  let pre := pre.getId
  let AE := mkConst (← liftCoreM <| realizeGlobalConstNoOverload a)
  let BE := mkConst (← liftCoreM <| realizeGlobalConstNoOverload b)
  let A ← liftCoreM <| natOfE AE
  let B ← liftCoreM <| natOfE BE
  let chs ← liftCoreM <| do listOfE (← valueOf (← realizeGlobalConstNoOverload cs))
  let c := layOf p.getNat d.getNat
  withSync do
    let listT := mkApp (mkConst ``List [0]) natE
    let exprList (S : List (Nat × Expr)) : Expr := S.foldr
      (fun (p : Nat × Expr) acc => mkApp3 (mkConst ``List.cons [0]) natE p.2 acc)
      (mkApp (mkConst ``List.nil [0]) natE)
    addDef (pre ++ `SONE) natE (bigLit c.ONE)
    let one := mkConst (pre ++ `SONE)
    let mut S : List (Nat × Expr) := [(A, AE), (B, BE)]
    addDef (pre ++ `S0) listT (exprList S)
    let mut i := 0
    for ch in chs do
      let (nE, rest) ← pairOfE ch
      let (opsE, outE) ← pairOfE rest
      let ops ← (← listOfE opsE).mapM fun o => do (← listOfE o).mapM natOfE
      S ← runChunkF c pre (i + 1) one S (← natOfE nE) ops (← (← listOfE outE).mapM natOfE)
      i := i + 1
      addDef (pre ++ Name.mkSimple s!"S{i}") listT (exprList S)
    let sl := (List.range (i + 1)).foldr
      (fun k acc => mkApp3 (mkConst ``List.cons [0]) listT
        (mkConst (pre ++ Name.mkSimple s!"S{k}")) acc)
      (mkApp (mkConst ``List.nil [0]) listT)
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT) sl

meta def canonLayF (c : LayV) (X : Nat) : Bool :=
  X >>> (c.d * c.S) == 0 && X &&& c.H == 0 && c.red c.L c.H X == X

meta unsafe def evalWord (n : Name) : CoreM (List (Nat × Nat)) :=
  evalConst (List (Nat × Nat)) n

elab "#lay_wsegs_f " pre:ident p:num d:num s:ident i:ident w:ident k:num : command => do
  let pre := pre.getId
  let c := layOf p.getNat d.getNat
  let k := k.getNat
  let S ← liftCoreM <| do
    (← listOfE (← valueOf (← realizeGlobalConstNoOverload s))).mapM natOfE
  let I ← liftCoreM <| do
    (← listOfE (← valueOf (← realizeGlobalConstNoOverload i))).mapM fun e =>
      match e.consumeMData.nat? with
      | some x => pure x
      | none => natOfE e
  let get (r : Nat) : Nat := match (I.zip S).find? (·.1 == r) with
    | some (_, v) => v
    | none => c.ONE
  let wd ← liftCoreM <| unsafe evalWord (← liftCoreM <| realizeGlobalConstNoOverload w)
  let nseg := (wd.length + k - 1) / k
  withSync do
    let mut acc := c.ONE
    let mut first := true
    let mut ws : Array Nat := Array.replicate nseg 0
    for j in [0:nseg] do
      let i := nseg - 1 - j
      for q in ((wd.drop (i * k)).take k).reverse do
        let y := powF c (get q.1) q.2
        acc := if first && canonLayF c y then y else mulF c y acc
        first := false
      ws := ws.set! i acc
    for i in [0:nseg] do
      addDef (pre ++ Name.mkSimple s!"W{i}") natE (bigLit ws[i]!)
    let wl := (List.range nseg).foldr
      (fun i acc => mkApp3 (mkConst ``List.cons [0]) natE
        (mkConst (pre ++ Name.mkSimple s!"W{i}")) acc)
      (mkApp (mkConst ``List.nil [0]) natE)
    addDef (pre ++ `WL) (mkApp (mkConst ``List [0]) natE) wl

end CFSG.KC.LaySnapsChunksF

end
