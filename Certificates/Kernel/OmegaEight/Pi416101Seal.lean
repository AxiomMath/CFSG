module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

elab "#kc_seal_list " n:ident e:ident len:num w:num : command => do
  let encN ← liftCoreM <| realizeGlobalConstNoOverload e
  CFSG.KC.Load.withSync do
    let env ← getEnv
    let v ← match Kernel.whnf env {} (mkConst encN) with
      | .ok (.lit (.natVal v)) => pure v
      | .ok _ => throwError "#kc_seal_list: {encN} does not reduce to a literal"
      | .error _ => throwError "#kc_seal_list: kernel error reducing {encN}"
    let m := 2 ^ w.getNat
    let mut x := v
    let mut xs : Array Expr := #[]
    for _ in [0:len.getNat] do
      xs := xs.push (mkRawNatLit (x % m))
      x := x / m
    unless x == 0 do throwError "#kc_seal_list: {encN} has more than {len.getNat} fields"
    CFSG.KC.Load.addDef n.getId (CFSG.KC.Load.listNatE) (CFSG.KC.Load.mkNatList xs) true
