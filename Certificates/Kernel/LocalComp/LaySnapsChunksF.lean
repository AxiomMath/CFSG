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
  if e == 0 then return c.ONE
  let mut acc := X
  for _ in [1:e] do acc := mulF c acc X
  return acc

meta def runChunkF (c : LayV) (S : List Nat) (n : Nat) (ops : List (List Nat)) (out : List Nat) :
    CoreM (List Nat) := do
  let mut R : Array Nat := (S ++ List.replicate (n - S.length) c.ONE).toArray
  for o in ops do
    match o with
    | [0, i, j, k] => R := R.set! k (mulF c (R.getD i c.ONE) (R.getD j c.ONE))
    | [e, i, _, k] => R := R.set! k (powF c (R.getD i c.ONE) e)
    | _ => throwError "#lay_snaps_chunks_f: not an operation: {o}"
  return out.map fun r => R.getD r c.ONE

elab "#lay_snaps_chunks_f " pre:ident p:num d:num a:ident b:ident cs:ident : command => do
  let pre := pre.getId
  let A ← liftCoreM <| do natOfE (← valueOf (← realizeGlobalConstNoOverload a))
  let B ← liftCoreM <| do natOfE (← valueOf (← realizeGlobalConstNoOverload b))
  let chs ← liftCoreM <| do listOfE (← valueOf (← realizeGlobalConstNoOverload cs))
  let c := layOf p.getNat d.getNat
  withSync do
    let listT := mkApp (mkConst ``List [0]) natE
    let mut S : List Nat := [A, B]
    addDef (pre ++ `S0) listT (natList S)
    let mut i := 0
    for ch in chs do
      let (nE, rest) ← pairOfE ch
      let (opsE, outE) ← pairOfE rest
      let ops ← (← listOfE opsE).mapM fun o => do (← listOfE o).mapM natOfE
      S ← runChunkF c S (← natOfE nE) ops (← (← listOfE outE).mapM natOfE)
      i := i + 1
      addDef (pre ++ Name.mkSimple s!"S{i}") listT (natList S)
    let sl := (List.range (i + 1)).foldr
      (fun k acc => mkApp3 (mkConst ``List.cons [0]) listT
        (mkConst (pre ++ Name.mkSimple s!"S{k}")) acc)
      (mkApp (mkConst ``List.nil [0]) listT)
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT) sl

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
    let mut ws : Array Nat := Array.replicate nseg 0
    for j in [0:nseg] do
      let i := nseg - 1 - j
      for q in ((wd.drop (i * k)).take k).reverse do
        acc := mulF c (powF c (get q.1) q.2) acc
      ws := ws.set! i acc
    for i in [0:nseg] do
      addDef (pre ++ Name.mkSimple s!"W{i}") natE (lit ws[i]!)
    let wl := (List.range nseg).foldr
      (fun i acc => mkApp3 (mkConst ``List.cons [0]) natE
        (mkConst (pre ++ Name.mkSimple s!"W{i}")) acc)
      (mkApp (mkConst ``List.nil [0]) natE)
    addDef (pre ++ `WL) (mkApp (mkConst ``List [0]) natE) wl

end CFSG.KC.LaySnapsChunksF

end
