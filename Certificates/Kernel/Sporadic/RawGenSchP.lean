module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Data.Kernel.Spor.RawSchP
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchP

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit

meta def sch2T (c : Ctx) (CH : Nat) (iE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK2)
    #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS,
      c.k `BP, lit c.nb, iE, c.steps iE, mulE sE (lit CH), lit CH])

meta def ltPf (a b : Nat) : Expr :=
  mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) (lit (a + 1)) (lit b))
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

end CFSG.KS.RawGenSchP

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchP in
elab "#ks_rawchain_sl2_schp " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"sq{ii.getNat}_{s}") (sch2T c CH (lit ii.getNat) (lit s))

end
