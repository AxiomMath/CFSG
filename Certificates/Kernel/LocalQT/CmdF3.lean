module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.LocalQT.SecF3
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Kernel.LocalQT.Cmd

public section

open Lean Elab Command Meta

namespace CFSG.KC.LQT.CmdF3

open CFSG.KC.LQT.Cmd

meta def natOf (n : Name) : CoreM Nat := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  let .lit (.natVal k) := v.value.consumeMData | throwError "{n} is not a literal"
  return k

meta def stepF (pre : Name) (K : Nat) : Expr :=
  let lay := mkConst (pre ++ `lay)
  let d := mkApp (mkConst ``CFSG.KC.LQT.Lay.d) lay
  mkAppN (mkConst ``CFSG.KC.LQT.stepF3)
    #[lay, lit K, mkApp2 (mkConst ``CFSG.KS.F3L.spreadE) d d, mkConst (pre ++ `V),
      mkConst (pre ++ `P)]

elab "#lqt_sr_steps3 " pre:ident K:num lo:num hi:num : command => do
  let pre := pre.getId
  withSync do
    let N ← natOf (pre ++ `N)
    for k in [max lo.getNat 3:min hi.getNat N] do
      addTrue (pre ++ Name.mkSimple s!"t{k}") (mkApp (stepF pre K.getNat) (lit k))

elab "#lqt_sr_chain3 " pre:ident K:num : command => do
  let pre := pre.getId
  withSync do
    let N ← natOf (pre ++ `N)
    let f := stepF pre K.getNat
    let mut pf := mkApp (mkConst ``CFSG.KC.LQT.steps_three) f
    for k in [3:N] do
      pf := mkAppN (mkConst ``CFSG.KC.LQT.steps_succ)
        #[f, lit k, pf, mkConst (pre ++ Name.mkSimple s!"t{k}")]
    addThm (pre ++ `steps3) (mkApp2 (mkConst ``CFSG.KC.LQT.StepsTo) f (lit N)) pf

end CFSG.KC.LQT.CmdF3

end
