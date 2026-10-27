module

public import Certificates.Kernel.Sporadic.RawGenSchPU
public import CFSG.Certificates.Kernel.Spor.RawSchUSplit
public meta import Certificates.Kernel.Sporadic.RawGenSchPU
public meta import Certificates.Kernel.Sporadic.RawGenSchPF
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchPUS

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchPF

meta def schUArgs (c : Ctx) (D : Nat) (iE : Expr) : Array Expr :=
  #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, c.k `U, lit c.kS,
    c.k `BP, lit D, lit c.nb, iE, fwE c iE]

meta def subT (c : Ctx) (D : Nat) (iE : Expr) (h₀ cnt : Nat) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK2U) (schUArgs c D iE ++ #[lit h₀, lit cnt]))

end CFSG.KS.RawGenSchPUS

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchPU
  CFSG.KS.RawGenSchPUS in
elab "#ks_rawchain_sl2_schpus " pre:ident ii:num lo:num hi:num bb:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  let D ← natOf (P ++ `pD)
  let B := bb.getNat
  if B == 0 || CH % B != 0 then
    throwError "#ks_rawchain_sl2_schpus: {B} does not divide the slice size {CH}"
  let i := ii.getNat
  let iE := lit i
  withSync do
    for s in [lo.getNat:hi.getNat] do
      let h₀ := s * CH
      let nm0 := P ++ Name.mkSimple s!"su{i}_{s}_0"
      addRefl nm0 (subT c D iE h₀ B)
      let mut pf := mkConst nm0
      for j in [1:CH / B] do
        let nm := P ++ Name.mkSimple s!"su{i}_{s}_{j}"
        addRefl nm (subT c D iE (h₀ + j * B) B)
        pf := mkAppN (mkConst ``CFSG.KS.Raw.schK2U_split)
          (schUArgs c D iE ++ #[lit h₀, lit (j * B), lit B, pf, mkConst nm])
      addThm (P ++ Name.mkSimple s!"su{i}_{s}") (sch2uT c CH D iE (lit s)) pf

end
