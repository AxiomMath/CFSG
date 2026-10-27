module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.SmallOddCore.J2CentralizerDInputs
public import Certificates.Data.Kernel.Spor.CntC
public import CFSG.Assembly.Defs
public import Certificates.Kernel.SporSch.GenSetReplay

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kcntc3 " pre:ident pch:ident nn:num ww:num lvId:ident gsId:ident dpId:ident :
    command => do
  let P := pre.getId
  let Pch := pch.getId
  let n := nn.getNat
  let w := ww.getNat
  let cn (s : Ident) := liftCoreM <| realizeGlobalConstNoOverload s
  let lvN ← cn lvId
  let gsN ← cn gsId
  let dpN ← cn dpId
  let levels ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) lvN
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) gsN
  let L0 := levels[0]!
  let L1 := levels[1]!
  let L2 := levels[2]!
  let cs := (Array.range L0.pts.size).map fun k0 => Id.run do
    let t0 := L0.tr[k0]!
    let mut a := 0
    for k1 in [0:L1.pts.size] do
      for k2 in [0:L2.pts.size] do
        if CFSG.Sporadic.SmallOddCore.commW n gs [L2.tr[k2]!, L1.tr[k1]!, t0] then
          a := a + 1
    return a
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `CS) cs
    let ty := fun (q : Expr) => mkApp3 (mkConst ``Eq [1]) natT
      (app ``CFSG.KS.SporSch.cntC3 #[lit n, lit w, mkConst (Pch ++ `LR), mkConst (Pch ++ `TR),
        mkConst dpN, q])
      (mkApp (mkConst (P ++ `CS)) q)
    for q in [0:cs.size] do
      let nm := P ++ Name.mkSimple ("k" ++ toString q)
      let pf := mkApp2 (mkConst ``Eq.refl [1]) natT (mkApp (mkConst (P ++ `CS)) (lit q))
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty (lit q), value := pf }
    let lam := mkLambda `q .default natT (ty (mkBVar 0))
    let v := forallChain lam cs.size fun q => mkConst (P ++ Name.mkSimple ("k" ++ toString q))
    let tyAll := forallLt cs.size ty
    CFSG.KC.addThmDecl <| { name := P ++ `hk, levelParams := [], type := tyAll, value := v }
    addDef (P ++ `c0) natT (lit cs.size)

end
