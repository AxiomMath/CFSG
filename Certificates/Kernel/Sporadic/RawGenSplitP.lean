module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Certificates.Kernel.Spor.RawSlPSound
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_lvp " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  let i := ii.getNat
  let iE := lit i
  let hsz := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      let sE := lit s
      let args := #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `TR, c.k `TRI, lit c.kS,
        c.steps iE, mkApp (c.k `LR) iE, mulE sE (lit LCH), lit LCH]
      let pN := P ++ Name.mkSimple s!"lsP{i}_{s}"
      addRefl pN (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlKP) args))
      let v := mkAppN (mkConst ``CFSG.KS.Raw.lvSlK_of_P)
        #[c.nE, c.wE, c.k `S, c.k `SI, c.k `TR, c.k `TRI, lit c.kS, c.steps iE,
          mkApp (c.k `LR) iE, mulE sE (lit LCH), lit LCH, hsz, mkConst pN]
      let nm := P ++ Name.mkSimple s!"ls{i}_{s}"
      addThm nm (lvSlT c LCH iE sE) v

end
