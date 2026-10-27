module

public meta import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.LocalComp.Replay
public import Certificates.Kernel.LocalQT.Cmd

public section

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native

namespace CFSG.KC.LQT.Cmd

meta def targets (nregs : Nat) (prog : List Op) : Array Nat × Array Nat := Id.run do
  let mut ops : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
  let mut regs : Array Nat :=
    (Array.range nregs).map fun r => if r == 0 then 0 else if r == 1 then 1 else 2
  let mut out : Array Nat := #[]
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
      out := out.push r
    | .pow e i k =>
      if e == 0 then
        regs := regs.set! k 2
        out := out.push 2
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
        out := out.push res.get!
  return (out, regs)

end CFSG.KC.LQT.Cmd

elab "#lqt_sr_replay " pre:ident dm:ident dr:ident : command => do
  let pre := pre.getId
  let D ← liftCoreM <| unsafe evalData dm.getId
  withSync do
    let (tt, regs) := targets D.nregs D.prog
    addSel (pre ++ `TT) (fun s => lit tt[s]!) tt.size
    let O := D.outs.toArray.map fun r => regs[r]!
    addSel (pre ++ `RO) (fun i => lit O[i]!) O.size
    let t := D.tests.headD 0
    let W := mkLambda `n .default natE (lit t)
    addTrue (pre ++ `replay) (mkAppN (mkConst ``CFSG.KC.LocalComp.Replay.replayOK)
      #[mkConst (pre ++ `lay), mkConst (pre ++ `V), mkConst (pre ++ `P), mkConst (pre ++ `TT),
        mkConst (pre ++ `N), mkConst dr.getId, mkConst (pre ++ `RO), W])
