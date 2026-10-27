module

public import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_each " pre:ident fId:ident kk:num : command => do
  let P := pre.getId
  let k := kk.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let fE := mkConst fN
  liftCoreM <| withOptions (Elab.async.set · false) do
    for i in [0:k] do
      let nm := P ++ Name.mkSimple s!"c{i}"
      let tyI := isTrue (mkApp fE (lit i))
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyI, value := reflBoolTrue }
    let pE := mkLambda `i .default natT (isTrue (mkApp fE (mkBVar 0)))
    let v := forallChain pE k fun i => mkConst (P ++ Name.mkSimple s!"c{i}")
    let ty := mkForall `i .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit k])
      (isTrue (mkApp fE (mkBVar 1))))
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := v }

end
