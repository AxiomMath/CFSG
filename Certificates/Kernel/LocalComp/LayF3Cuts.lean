module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnaps
public meta import Certificates.Kernel.LocalComp.LaySnapsChunks
public meta import Certificates.Kernel.LocalComp.ExprRead
public import Certificates.Data.Kernel.OpsLayF3
public import Certificates.Kernel.LocalQT.Cmd

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native

public section

namespace CFSG.KC.LayF3Cuts

meta def gath (w d X : Nat) : Nat × Nat := Id.run do
  let S := w * d
  let mS := (1 <<< S) - 1
  let mw := (1 <<< w) - 1
  let mut rows : Array Nat := Array.mkEmpty d
  let mut r := X
  for _ in [0:d] do
    rows := rows.push (r &&& mS)
    r := r >>> S
  let mut ps : Array Nat := Array.mkEmpty d
  let mut ms : Array Nat := Array.mkEmpty d
  for row in rows do
    let mut x := row
    let mut p := 0
    let mut m := 0
    for j in [0:d] do
      let e := x &&& mw
      x := x >>> w
      if e &&& 1 == 1 then p := p ||| (1 <<< j)
      if (e >>> 1) &&& 1 == 1 then m := m ||| (1 <<< j)
    ps := ps.push p
    ms := ms.push m
  let join (a : Array Nat) : Nat := Id.run do
    let mut acc := 0
    for i in [0:d] do
      let j := d - 1 - i
      acc := (acc <<< d) ||| a[j]!
    return acc
  return (join ps, join ms)

meta def vE (pm : Nat × Nat) : Expr :=
  mkApp2 (mkConst ``CFSG.F3.Native.V.mk) (lit pm.1) (lit pm.2)

meta def vList (xs : List (Nat × Nat)) : Expr :=
  let vT := mkConst ``CFSG.F3.Native.V
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) vT (vE x) acc)
    (mkApp (mkConst ``List.nil [0]) vT)

meta def opOfL : List Nat → Op
  | [0, i, j, k] => .mul i j k
  | [e, i, _, k] => .pow e i k
  | _ => .mul 0 0 0

meta def step (c : LayV) (R : Array Nat) : Op → Array Nat
  | .mul i j t => if t < R.size then R.set! t (c.mul (R.getD i c.ONE) (R.getD j c.ONE)) else R
  | .pow e i t =>
    if t < R.size then R.set! t (c.pow (R.getD i c.ONE) e) else R

meta def cutsCore (pre : Name) (c : LayV) (R0 : Array Nat) (ops : List Op) (cuts : List Nat) :
    CoreM Unit := do
  let mut R := R0
  let mut done := 0
  let mut j := 1
  for a in cuts do
    if a < done then throwError "#lay_f3_cuts: cuts must increase"
    for o in (ops.drop done).take (a - done) do
      R := step c R o
    done := a
    let vs := R.toList.map (gath c.w c.d)
    addDef (pre ++ Name.mkSimple s!"M{j}") (mkApp (mkConst ``List [0]) (mkConst ``CFSG.F3.Native.V))
      (vList vs)
    j := j + 1

meta def natsOf (n : Name) : CoreM (List Nat) := do
  (← CFSG.KC.LaySnapsChunks.listOfE (← CFSG.KC.LaySnapsChunks.valueOf n)).mapM
    CFSG.KC.LaySnapsChunks.natOfE

elab "#lay_f3_cuts_v " pre:ident p:num d:num _K:num regs:ident cs:ident k:num
    "[" cuts:num,* "]" : command => do
  let pre := pre.getId
  let c := layOf p.getNat d.getNat
  let S ← liftCoreM <| natsOf (← liftCoreM <| realizeGlobalConstNoOverload regs)
  let chs ← liftCoreM <| do
    CFSG.KC.LaySnapsChunks.listOfE
      (← CFSG.KC.LaySnapsChunks.valueOf (← realizeGlobalConstNoOverload cs))
  let some ch := chs[k.getNat]? | throwError "#lay_f3_cuts_v: no chunk {k.getNat}"
  let (nE, rest) ← liftCoreM <| CFSG.KC.LaySnapsChunks.pairOfE ch
  let (opsE, _) ← liftCoreM <| CFSG.KC.LaySnapsChunks.pairOfE rest
  let n ← liftCoreM <| CFSG.KC.LaySnapsChunks.natOfE nE
  let ops ← liftCoreM do
    let os ← CFSG.KC.LaySnapsChunks.listOfE opsE
    os.mapM fun o => do
      let l ← CFSG.KC.LaySnapsChunks.listOfE o
      return opOfL (← l.mapM CFSG.KC.LaySnapsChunks.natOfE)
  let R0 := (S ++ List.replicate (n - S.length) c.ONE).toArray
  withSync <| cutsCore pre c R0 ops (cuts.getElems.toList.map (·.getNat))

elab "#lay_f3_cuts_l " pre:ident p:num d:num _K:num regs:ident prog:ident m:num i:num
    "[" cuts:num,* "]" : command => do
  let pre := pre.getId
  let c := layOf p.getNat d.getNat
  let S ← liftCoreM <| natsOf (← liftCoreM <| realizeGlobalConstNoOverload regs)
  let progN ← liftCoreM <| realizeGlobalConstNoOverload prog
  let ops ← liftTermElabM <| CFSG.KC.ExprRead.progW (mkConst progN)
  let ops := (ops.drop (i.getNat * m.getNat)).take m.getNat
  withSync <| cutsCore pre c S.toArray ops (cuts.getElems.toList.map (·.getNat))

end CFSG.KC.LayF3Cuts

end
