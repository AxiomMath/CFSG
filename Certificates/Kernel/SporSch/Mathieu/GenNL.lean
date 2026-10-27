module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Data.Kernel.SporSch.NoLayer

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_packs " pre:ident ww:num cId:ident : command => do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload cId
  let C ← liftTermElabM <| unsafe evalConst (List (List Nat)) nm
  let w := ww.getNat
  withSync do
    addDef pre.getId listT (listE (C.map fun l => pack w l.toArray))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_nlk " pre:ident qq:ident nn:num ww:num nbN:num eId:ident bN:num nBN:num :
    command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let B := bN.getNat
  let NB := nBN.getNat
  let EN ← liftCoreM <| realizeGlobalConstNoOverload eId
  let nE := lit n
  let wE := lit w
  let stmt := fun (loE : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.MOC.nlK)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE,
      mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      lit nbN.getNat, mkConst EN, loE, lit B]
  withSync do
    for s in [0:NB] do
      let nm := P ++ Name.mkSimple s!"c{s}"
      let ty := isTrue (stmt (lit (s * B)))
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
    let pE := mkLambda `s .default natT (isTrue (stmt (mulE (mkBVar 0) (lit B))))
    let hV := forallLt pE NB fun s => mkConst (P ++ Name.mkSimple s!"c{s}")
    let hT := mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit NB])
      (isTrue (stmt (mulE (mkBVar 1) (lit B)))))
    CFSG.KC.addThmDecl <| { name := P ++ `hK, levelParams := [], type := hT, value := hV }

end
