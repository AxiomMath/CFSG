module

public import Certificates.Kernel.Sporadic.ON.Gen
public meta import Certificates.Kernel.Sporadic.ON.Gen
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.ONGen CFSG.ONSchreier.Native in
elab "#kon_levels " pre:ident sId:ident bId:ident kk:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let n := S[0]!.size
  let Ls := cLevels n base (allSteps S (pinvs n S) base)
  withSync do
    for i in [0:kk.getNat] do
      let L := Ls[i]!
      addTree (P ++ Name.mkSimple s!"PTS{i}") (leaves 18 6 L.pts)
      addTree (P ++ Name.mkSimple s!"POS{i}") (leaves 18 6 L.pos)
      addTree (P ++ Name.mkSimple s!"PAR{i}") (leaves 18 6 L.par)
      addTree (P ++ Name.mkSimple s!"LAB{i}") (leaves 18 6 L.lab)
      addDef (P ++ Name.mkSimple s!"M{i}") natT (lit L.pts.size)

end
