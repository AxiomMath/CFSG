module

public meta import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Kernel.LocalQT.Cmd

public section

open Lean Elab Command Meta CFSG.KC.LQT.Cmd

elab "#lay_seeds " pre:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  withSync do
    let c := layOf p.getNat d.getNat
    let lay := mkConst (pre ++ `lay)
    addDef (pre ++ `lay) (mkConst ``CFSG.KC.LQT.Lay) c.expr
    addTrue (pre ++ `lay_ok) (mkApp (mkConst ``CFSG.KC.LQT.Lay.ok) lay)
    let s1 ← addChars (pre ++ `LA) sA.getId
    let s2 ← addChars (pre ++ `LB) sB.getId
    addDef (pre ++ `A) natE (lit (c.decode s1))
    addDef (pre ++ `B) natE (lit (c.decode s2))
    addTrue (pre ++ `decA) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkConst (pre ++ `A))
      (mkConst (pre ++ `LA)))
    addTrue (pre ++ `decB) (mkApp3 (mkConst ``CFSG.KC.LQT.decOK) lay (mkConst (pre ++ `B))
      (mkConst (pre ++ `LB)))
