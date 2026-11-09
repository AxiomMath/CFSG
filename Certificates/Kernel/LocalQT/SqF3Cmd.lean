module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnaps
public meta import Certificates.Kernel.LocalComp.LayF3Cuts
public meta import Certificates.Kernel.LocalComp.ExprRead
public import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.OpsLayF3

open Lean Elab Command Meta CFSG.KC.LQT.Cmd

public section

namespace CFSG.KC.LQT.SqF3

meta def vT : Expr := mkConst ``CFSG.F3.Native.V

elab "#lqt_sr_sq_vals " pre:ident dat:ident p:num d:num sA:ident sB:ident : command => do
  let pre := pre.getId
  let datN ← liftCoreM <| realizeGlobalConstNoOverload dat
  let D ← liftTermElabM <| CFSG.KC.ExprRead.sqW (mkApp (mkConst datN) (mkConst ``Unit.unit))
  withSync do
    let (c, vals, regs) ← addProgram pre p.getNat d.getNat sA.getId sB.getId D.nregs D.prog
    let ix := regs[D.rx]!
    let iy := regs[D.ry]!
    let ih := regs[D.rh]!
    for (nm, v) in [(`ix, ix), (`iy, iy), (`ih, ih)] do addDef (pre ++ nm) natE (lit v)
    let σ := sortOrder c D.r #[vals[ix]!, vals[iy]!] D.t
    addDef (pre ++ `sigma) (mkApp (mkConst ``List [0]) natE) (natList σ)
    let X := vals[ix]!
    let Y := vals[iy]!
    let H := vals[ih]!
    let pw (Z : Nat) (n : Nat) : Array Nat := Id.run do
      let mut out : Array Nat := #[c.ONE]
      for _ in [0:n] do out := out.push (c.mul out.back! Z)
      return out
    let xs := pw X (max D.r (max D.a D.b))
    let ys := pw Y (max D.r (max D.c D.d))
    let hs := pw H D.oh
    let rec_ (nm : String) (v : Nat) : CoreM Unit :=
      addDef (pre ++ Name.mkSimple s!"F{nm}") vT
        (CFSG.KC.LayF3Cuts.vE (CFSG.KC.LayF3Cuts.gath c.w c.d v))
    for k in [1:xs.size] do rec_ s!"x{k}" xs[k]!
    for k in [1:ys.size] do rec_ s!"y{k}" ys[k]!
    for k in [1:hs.size] do rec_ s!"h{k}" hs[k]!
    rec_ "xy" (c.mul X Y)
    rec_ "yx" (c.mul Y X)
    rec_ "hx" (c.mul H X)
    let w1 := c.mul xs[D.a]! ys[D.c]!
    rec_ "w1" w1
    rec_ "w1h" (c.mul w1 H)
    rec_ "hy" (c.mul H Y)
    let w2 := c.mul xs[D.b]! ys[D.d]!
    rec_ "w2" w2
    rec_ "w2h" (c.mul w2 H)

elab "#lqt_sr_sq_thm " pre:ident dat:ident h:ident : command => do
  let pre := pre.getId
  let datN ← liftCoreM <| realizeGlobalConstNoOverload dat
  let D ← liftTermElabM <| CFSG.KC.ExprRead.sqW (mkApp (mkConst datN) (mkConst ``Unit.unit))
  let hN ← liftCoreM <| realizeGlobalConstNoOverload h
  withSync do
    let nat (n : Name) : CoreM Nat := CFSG.KC.LaySnaps.natOf (pre ++ n)
    let ty := eqTrue (mkAppN (mkConst ``CFSG.KC.LQT.sqOK)
      #[mkConst (pre ++ `lay), mkConst (pre ++ `V), lit (← nat `N), lit (← nat `ix),
        lit (← nat `iy), lit (← nat `ih), lit D.r, lit D.oh, lit D.a, lit D.b, lit D.c, lit D.d,
        lit D.t, mkConst (pre ++ `sigma)])
    addThm (pre ++ `sq) ty (mkConst hN)

end CFSG.KC.LQT.SqF3

end
