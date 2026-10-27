module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public import Certificates.Kernel.SporSch.GenSetReplay

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kly_chainT " pre:ident nmI:ident qId:ident impId:ident g0:num g1:num rr:num : command => do
  let P := pre.getId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let impN ← liftCoreM <| realizeGlobalConstNoOverload impId
  let nm := nmI.getId.toString
  let R := rr.getNat
  let ty := fun q => isTrue (mkApp (mkConst qN) q)
  liftCoreM <| withOptions (Elab.async.set · false) do
    for g in [g0.getNat:g1.getNat] do
      for r in [0:R] do
        let nmq := P ++ Name.mkSimple s!"{nm}_{g}_{r}"
        let q := idxE (lit g) R (lit r)
        let v := mkApp2 (mkConst impN) q reflBoolTrue
        CFSG.KC.addThmDecl <| { name := nmq, levelParams := [], type := ty q, value := v }
      let lamR := mkLambda `r .default natT (ty (idxE (lit g) R (mkBVar 0)))
      let vR := forallChain lamR R fun r => mkConst (P ++ Name.mkSimple s!"{nm}_{g}_{r}")
      let nmg := P ++ Name.mkSimple s!"{nm}_{g}"
      let tyR := forallLt R fun r => ty (idxE (lit g) R r)
      CFSG.KC.addThmDecl <| { name := nmg, levelParams := [], type := tyR, value := vR }

end
