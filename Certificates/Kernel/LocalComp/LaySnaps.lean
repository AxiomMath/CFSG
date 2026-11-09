module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Kernel.LocalQT.Cmd

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native

public section

namespace CFSG.KC.LaySnaps

meta def natOf (n : Name) : CoreM Nat := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  match natOfLit? v.value with
  | some x => return x
  | none => throwError "{n} is not a Nat literal: {v.value}"

meta structure Val where
  pk : Nat
deriving Inhabited

meta def Val.ofPk (_c : LayV) (x : Nat) : Val := { pk := x }

meta def Val.mul (c : LayV) (a b : Val) : Val :=
  if c.p == 3 then { pk := CFSG.KC.LaySnapsChunksF.mulF c a.pk b.pk } else { pk := c.mul a.pk b.pk }

meta def Val.pack (_c : LayV) (a : Val) : Nat := a.pk

meta def layPow (c : LayV) (X : Val) (e : Nat) : Val := Id.run do
  let mut acc : Option Val := none
  let mut b := X
  let mut k := e
  while 0 < k do
    if k % 2 == 1 then
      acc := some (match acc with
        | none => b
        | some a => a.mul c b)
    k := k / 2
    if 0 < k then b := b.mul c b
  return acc.getD (Val.ofPk c c.ONE)

meta structure RunSt where
  ids : Array Nat
  vals : Array Val
  memo : Std.HashMap (Nat × Nat × Nat) Nat

meta def RunSt.put (s : RunSt) (t : Nat) (key : Nat × Nat × Nat) (val : Unit → Val) :
    RunSt × Nat :=
  match s.memo[key]? with
  | some v => ({ s with ids := s.ids.set! t v }, v)
  | none =>
    let v := s.vals.size
    ({ ids := s.ids.set! t v, vals := s.vals.push (val ()), memo := s.memo.insert key v }, v)

meta def runOps (c : LayV) (s : RunSt) (vs : Array Nat) (ops : List Op) : RunSt × Array Nat :=
  ops.foldl (fun (s, vs) o => match o with
    | .mul i j t =>
      let a := s.ids[i]!
      let b := s.ids[j]!
      let (s, v) := s.put t (0, a, b) fun _ => s.vals[a]!.mul c s.vals[b]!
      (s, vs.push v)
    | .pow e i t =>
      let a := s.ids[i]!
      let (s, v) := s.put t (e + 1, a, 0) fun _ => layPow c s.vals[a]! e
      (s, vs.push v)) (s, vs)

meta def RunSt.packV (c : LayV) (s : RunSt) (v : Nat) : RunSt × Nat :=
  let a := s.vals[v]!
  if a.pk != 0 then (s, a.pk) else
    let x := a.pack c
    ({ s with vals := s.vals.set! v { a with pk := x } }, x)

meta def RunSt.regs (c : LayV) (s : RunSt) : RunSt × List Nat :=
  s.ids.foldr (fun v (s, xs) => let (s, x) := s.packV c v; (s, x :: xs)) (s, [])

meta structure TabSt where
  seed : Nat × Nat × Nat × Nat
  st : RunSt
  rows : Array Name

meta initialize tabExt : EnvExtension (Option TabSt) ← registerEnvExtension (pure none)

meta def keyOf (m : Std.HashMap (Nat × Nat × Nat) Nat) (n : Nat) : Array (Nat × Nat × Nat) :=
  m.fold (fun ks k v => ks.set! v k) (Array.replicate n (0, 0, 0))

meta def btN : Name := `CFSG.KC.OpsLayTab.BTr

meta partial def btE (ty : Expr) (xs : Array Expr) : Expr :=
  if xs.size == 0 then mkApp (mkConst (btN ++ `nil)) ty
  else if xs.size == 1 then mkApp2 (mkConst (btN ++ `leaf)) ty xs[0]!
  else
    let ev := (Array.range ((xs.size + 1) / 2)).map fun i => xs[2 * i]!
    let od := (Array.range (xs.size / 2)).map fun i => xs[2 * i + 1]!
    mkApp3 (mkConst (btN ++ `node)) ty (btE ty ev) (btE ty od)

meta def packIds (ids : Array Nat) : Nat := ids.foldr (fun x acc => (acc <<< 16) ||| x) 0

meta unsafe def evalProg (n : Name) : CoreM (List Op) := evalConst (List Op) n

elab "#lay_snaps " pre:ident p:num d:num a:ident b:ident prog:ident n:num k:num : command => do
  let pre := pre.getId
  let A ← liftCoreM <| natOf (← liftCoreM <| realizeGlobalConstNoOverload a)
  let B ← liftCoreM <| natOf (← liftCoreM <| realizeGlobalConstNoOverload b)
  let ops ← liftCoreM <| unsafe evalProg (← liftCoreM <| realizeGlobalConstNoOverload prog)
  let c := layOf p.getNat d.getNat
  let n := n.getNat
  let k := k.getNat
  let m := (ops.length + k - 1) / k
  let seed := (p.getNat, d.getNat, A, B)
  withSync do
    let ids0 := (Array.range n).map fun r => min r 2
    let fresh : RunSt :=
      { ids := ids0, vals := #[A, B, c.ONE].map (Val.ofPk c), memo := {} }
    let (s0, rows0) := match tabExt.getState (← getEnv) with
      | some t => if t.seed == seed then ({ t.st with ids := ids0 }, t.rows) else (fresh, #[])
      | none => (fresh, #[])
    let mut s := s0
    let mut vs : Array Nat := #[]
    let listT := mkApp (mkConst ``List [0]) natE
    let (s1, r0) := s.regs c
    s := s1
    addDef (pre ++ `S0) listT (natList r0)
    for i in [0:m] do
      (s, vs) := runOps c s vs ((ops.drop (i * k)).take k)
      let (s1, ri) := s.regs c
      s := s1
      addDef (pre ++ Name.mkSimple s!"S{i + 1}") listT (natList ri)
    let sl := (List.range (m + 1)).foldr
      (fun i acc => mkApp3 (mkConst ``List.cons [0]) listT
        (mkConst (pre ++ Name.mkSimple s!"S{i}")) acc)
      (mkApp (mkConst ``List.nil [0]) listT)
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT) sl
    addDef (pre ++ `m) natE (lit m)
    let mut rows := rows0
    if (← getEnv).imports.any (·.module == `Certificates.Data.Kernel.OpsLayTab) then
      let N := s.vals.size
      for v in [0:N] do
        s := (s.packV c v).1
      let pks := s.vals.map (·.pk)
      let keys := keyOf s.memo N
      let rowT := mkApp (mkConst btN) natE
      let mut vRows : Array Expr := #[]
      for j in [0:(N + 63) / 64] do
        let full := (j + 1) * 64 ≤ N
        let nm ← if h : j < rows.size then pure rows[j] else do
          let nm := pre ++ Name.mkSimple s!"R{j}"
          let hi := min N ((j + 1) * 64)
          addDef nm rowT (btE natE ((pks.extract (j * 64) hi).map lit))
          if full then rows := rows.push nm
          pure nm
        vRows := vRows.push (mkConst nm)
      addDef (pre ++ `VT) (mkApp (mkConst btN) rowT) (btE rowT vRows)
      addDef (pre ++ `KT) natE (lit (keys.foldr (fun (c, a, b) acc =>
        (acc <<< 48) + ((c <<< 32) + (a <<< 16) + b)) 0))
      addDef (pre ++ `N) natE (lit N)
      addDef (pre ++ `I0) natE (lit (packIds ids0))
      addDef (pre ++ `IF) natE (lit (packIds s.ids))
      addDef (pre ++ `VS) listT (natList vs.toList)
    modifyEnv fun env => tabExt.setState env (some { seed, st := s, rows })

end CFSG.KC.LaySnaps

end
