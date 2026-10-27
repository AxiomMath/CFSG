module

public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.ReplayCmd
public import Certificates.Data.Kernel.LocalComp.CubParts
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public import Certificates.Kernel.LocalComp.ReplayCmd

public section

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native CFSG.KC.LocalComp.CubParts

namespace CFSG.KC.LQT.Cmd

open CFSG.SectionRank.Native in
meta unsafe def evalSecD (n : Name) : CoreM SecData := evalConst SecData n

meta def ssaOps (nregs : Nat) (prog : List Op) : Array (Nat × Nat) := Id.run do
  let mut ops : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
  let mut regs : Array Nat :=
    (Array.range nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  let mulI := fun (ops : Array (Nat × Nat)) (a b : Nat) =>
    match ops.findIdx? (· == (a, b)) with
    | some i => if i ≥ 3 then (ops, i) else (ops.push (a, b), ops.size)
    | none => (ops.push (a, b), ops.size)
  for o in prog do
    match o with
    | .mul i j k =>
      let (o', r) := mulI ops regs[i]! regs[j]!
      ops := o'
      regs := regs.set! k r
    | .pow e i k =>
      if e == 0 then regs := regs.set! k 2
      else
        let mut res : Option Nat := none
        let mut base := regs[i]!
        let mut e' := e
        while e' > 0 do
          if e' % 2 == 1 then
            match res with
            | none => res := some base
            | some r0 =>
              let (o', r) := mulI ops r0 base
              ops := o'
              res := some r
          e' := e' / 2
          if e' > 0 then
            let (o', r) := mulI ops base base
            ops := o'
            base := r
        regs := regs.set! k res.get!
  return ops

meta def natLitOf (n : Name) : CoreM Nat := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  match v.value with
  | .lit (.natVal k) => return k
  | _ => throwError "{n} is not a natural-number literal"

meta def vName (pre : Name) (k : Nat) : Name := pre ++ Name.mkSimple s!"V{k}"

meta def joinProgram (pre : Name) (p d : Nat) (nregs : Nat) (prog : List Op) :
    CoreM (LayV × Array Nat) := do
  let c := layOf p d
  let ops := ssaOps nregs prog
  let vals ← (Array.range ops.size).mapM fun k => natLitOf (vName pre k)
  let lay := mkConst (pre ++ `lay)
  addSel (pre ++ `V) (fun k => mkConst (vName pre k)) ops.size
  addDef (pre ++ `N) natE (lit ops.size)
  for k in [3:ops.size] do
    let (a, b) := ops[k]!
    addDef (pre ++ Name.mkSimple s!"P{k}") natE (lit (a + (b <<< 20)))
  addSel (pre ++ `P) (fun k => if k < 3 then lit 0 else mkConst (pre ++ Name.mkSimple s!"P{k}"))
    ops.size
  let V := mkConst (pre ++ `V)
  let P := mkConst (pre ++ `P)
  addTrue (pre ++ `decA) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkApp V (lit 0)) (mkConst (pre ++ `LA)))
  addTrue (pre ++ `decB) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkApp V (lit 1)) (mkConst (pre ++ `LB)))
  let oneTy := mkApp3 (mkConst ``Eq [1]) natE (mkApp V (lit 2)) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ONE) lay)
  addThm (pre ++ `one) oneTy (mkApp2 (mkConst ``Eq.refl [1]) natE (mkApp V (lit 2)))
  let f := mkApp3 (mkConst ``CFSG.KC.LQT.stepOK) lay V P
  let rflN := fun (e : Expr) => mkApp2 (mkConst ``Eq.refl [1]) natE e
  let mut pf := mkApp (mkConst ``CFSG.KC.LQT.steps_three) f
  for k in [3:ops.size] do
    let (a, b) := ops[k]!
    let q := a + (b <<< 20)
    let tn := pre ++ Name.mkSimple s!"s{k}"
    let val := mkAppN (mkConst ``stepOK_of_vals)
      #[lay, V, P, lit k, lit a, lit b, lit q, mkConst (vName pre k), mkConst (vName pre a),
        mkConst (vName pre b), rflN (mkApp P (lit k)), reflBoolTrue, reflBoolTrue,
        rflN (mkApp V (lit k)), rflN (mkApp V (lit a)), rflN (mkApp V (lit b)),
        mkConst (pre ++ Name.mkSimple s!"m{k}")]
    addThm tn (eqTrue (mkApp f (lit k))) val
    pf := mkAppN (mkConst ``CFSG.KC.LQT.steps_succ) #[f, lit k, pf, mkConst tn]
  addThm (pre ++ `steps) (mkApp2 (mkConst ``CFSG.KC.LQT.StepsTo) f (lit ops.size)) pf
  return (c, vals)

meta def addReplay (pre : Name) (D : Data) (dr : Name) : CoreM Unit := do
  let (tt, regs) := targets D.nregs D.prog
  addSel (pre ++ `TT) (fun s => lit tt[s]!) tt.size
  let O := D.outs.toArray.map fun r => regs[r]!
  addSel (pre ++ `RO) (fun i => lit O[i]!) O.size
  let t := D.tests.headD 0
  addTrue (pre ++ `replay) (mkAppN (mkConst ``CFSG.KC.LocalComp.Replay.replayOK)
    #[mkConst (pre ++ `lay), mkConst (pre ++ `V), mkConst (pre ++ `P), mkConst (pre ++ `TT),
      mkConst (pre ++ `N), mkConst dr, mkConst (pre ++ `RO), mkLambda `n .default natE (lit t)])

meta def vtabOf (c : LayV) (b : Nat) (X : Array Nat) (t : Nat) : Array Nat × Array Nat := Id.run do
  let M := b ^ X.size
  let mut U : Array Nat := #[c.unit t]
  let mut HI : Array Nat := #[0]
  let mut h := 0
  for n in [1:M] do
    while b ^ (h + 1) ≤ n do h := h + 1
    U := U.push (c.vec U[n - b ^ h]! X[h]!)
    HI := HI.push h
  return (U, HI)

meta def addVTab (pre : Name) (c : LayV) (b : Nat) (X : Array Nat) (Xe : Expr) (t : Nat) :
    CoreM (Array Nat) := do
  let CH := 10
  let (U, HI) := vtabOf c b X t
  addSel (pre ++ `U) (fun n => lit U[n]!) U.size
  addSel (pre ++ `HI) (fun n => lit HI[n]!) HI.size
  let lay := mkConst (pre ++ `lay)
  addTrue (pre ++ `vt0) (mkApp3 (mkConst ``vt0) lay (lit t) (mkConst (pre ++ `U)))
  let NS := (U.size - 1 + CH - 1) / CH
  let f := mkLambda `s .default natE (mkAppN (mkConst ``vtabK)
    #[lay, lit b, Xe, lit X.size, mkConst (pre ++ `U), mkConst (pre ++ `HI),
      mkApp2 (mkConst ``Nat.mul) (lit CH) (.bvar 0), lit CH])
  let mut pf := mkApp (mkConst ``chunks_zero) f
  for s in [0:NS] do
    let tn := pre ++ Name.mkSimple s!"vc{s}"
    addTrue tn (mkApp f (lit s))
    pf := mkAppN (mkConst ``chunks_succ) #[f, lit s, pf, mkConst tn]
  addThm (pre ++ `vtab) (mkApp2 (mkConst ``ChunksTo) f (lit NS)) pf
  return U

end CFSG.KC.LQT.Cmd

elab "#lqt_prog_part " pre:ident dat:ident p:num d:num sA:ident sB:ident i:num K:num :
    command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalData dat.getId
  withSync do
    let c := layOf p.getNat d.getNat
    let ops := ssaOps D.nregs D.prog
    let M := ops.size - 3
    let i := i.getNat
    let K := K.getNat
    let lo := 3 + i * M / K
    let hi := 3 + (i + 1) * M / K
    let lay := mkConst (pre ++ `lay)
    if i == 0 then
      addDef (pre ++ `lay) (mkConst ``CFSG.KC.LQT.Lay) c.expr
      addTrue (pre ++ `lay_ok) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ok) lay)
      let s1 ← addChars (pre ++ `LA) sA.getId
      let s2 ← addChars (pre ++ `LB) sB.getId
      addDef (vName pre 0) natE (lit (c.decode s1))
      addDef (vName pre 1) natE (lit (c.decode s2))
      addDef (vName pre 2) natE (lit c.ONE)
    let mut loc : Std.HashMap Nat Nat := {}
    for k in [lo:hi] do
      let (a, b) := ops[k]!
      let x ← match loc.get? a with
        | some v => pure v
        | none => natLitOf (vName pre a)
      let y ← match loc.get? b with
        | some v => pure v
        | none => natLitOf (vName pre b)
      let v := c.mul x y
      loc := loc.insert k v
      addDef (vName pre k) natE (lit v)
      addTrue (pre ++ Name.mkSimple s!"m{k}") (mkApp2 (mkConst ``Nat.beq) (mkConst (vName pre k))
        (mkApp3 (mkConst ``CFSG.KC.LQT.Lay.mul) lay (mkConst (vName pre a)) (mkConst (vName pre b))))

elab "#lqt_sr_cubx " pre:ident dat:ident dr:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalCub dat.getId
  withSync do
    let E := D.extData
    let (c, vals) ← joinProgram pre p.getNat d.getNat E.nregs E.prog
    let (tt, regs) := targets E.nregs E.prog
    let I := tt.extract D.prog.length tt.size
    addSel (pre ++ `I) (fun k => lit I[k]!) I.size
    addReplay pre D.asData dr.getId
    let lay := mkConst (pre ++ `lay)
    let V := mkConst (pre ++ `V)
    let Ie := mkConst (pre ++ `I)
    let O := fun k => mkApp (mkConst (pre ++ `RO)) (lit k)
    addTrue (pre ++ `parts) (mkAppN (mkConst ``cubPartsOK)
      #[lay, V, mkConst (pre ++ `P), mkConst (pre ++ `N), O 0, O 1, O 2, Ie, lit D.r, lit D.oh,
        lit D.a, lit D.b, lit D.c, lit D.d, lit D.k, lit D.l, lit D.μ, lit D.t])
    let X := #[vals[regs[D.rx]!]!, vals[regs[D.ry]!]!, vals[I[7]!]!]
    let Xe := mkApp3 (mkConst ``CFSG.KC.LQT.sel3) (mkApp V (O 0)) (mkApp V (O 1))
      (mkApp V (mkApp Ie (lit 7)))
    let U ← addVTab pre c D.r X Xe D.t
    let σ := ((List.range U.size).map fun n => (U[n]!, n)).mergeSort (fun a b => a.1 ≤ b.1)
      |>.map (·.2)
    addDef (pre ++ `sigma) (mkApp (mkConst ``List [0]) natE) (natList σ)
    addTrue (pre ++ `sort) (mkAppN (mkConst ``CFSG.KC.LQT.sortRun)
      #[mkApp2 (mkConst ``Nat.pow) (lit D.r) (lit 3), mkConst (pre ++ `U),
        mkConst (pre ++ `sigma), lit 0, lit 0])

elab "#lqt_sr_secx " pre:ident dat:ident dr:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalSecD dat.getId
  withSync do
    let r := D.outs.length
    let B := 1 + 3 * r
    let E := D.extData
    let (c, vals) ← joinProgram pre p.getNat d.getNat E.nregs E.prog
    let (tt, regs) := targets E.nregs E.prog
    let L := D.prog.length
    let mut J : Array Nat := Array.replicate (B + 3 * r * r) 0
    for e in [0:B] do J := J.set! e tt[L + e]!
    let mut s := L + B
    for i in [0:r] do
      for j in [i + 1:r] do
        for e in [0:3] do J := J.set! (B + 3 * (r * i + j) + e) tt[s + e]!
        s := s + 3
    addSel (pre ++ `J) (fun k => lit J[k]!) J.size
    addReplay pre D.asData dr.getId
    let lay := mkConst (pre ++ `lay)
    let V := mkConst (pre ++ `V)
    let RO := mkConst (pre ++ `RO)
    addTrue (pre ++ `parts) (mkAppN (mkConst ``secPartsOK)
      #[lay, V, mkConst (pre ++ `P), mkConst (pre ++ `N), RO, lit r, mkConst (pre ++ `J)])
    let X := D.outs.toArray.map fun o => vals[regs[o]!]!
    let Xe := mkLambda `i .default natE (mkApp V (mkApp RO (.bvar 0)))
    let t := D.tests.headD 0
    discard <| addVTab pre c 2 X Xe t
    addTrue (pre ++ `kmod) (mkAppN (mkConst ``kmodK)
      #[lay, mkConst (pre ++ `U), mkApp V (mkApp RO (lit r)), lit t, lit r])
