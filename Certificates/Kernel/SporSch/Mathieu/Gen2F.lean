module

public import Certificates.Kernel.SporSch.Mathieu.Gen2
public import Certificates.Data.Kernel.SporSch.MathieuOC2F
public meta import Certificates.Kernel.SporSch.Mathieu.Gen2

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_cntword2f " pre:ident qq:ident nn:num ww:num sId:ident bId:ident mxN:num myN:num
    wsId:ident RId:ident rId:ident : command => do
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let mx := mxN.getNat
  let my := myN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let r ← evalArr rId
  let wsN ← liftCoreM <| realizeGlobalConstNoOverload wsId
  let ws ← liftTermElabM <| unsafe evalConst (List (List Nat × Nat)) wsN
  let RN ← liftCoreM <| realizeGlobalConstNoOverload RId
  let L := levelsOf n S base
  let xi := powA r (mx - 1)
  let wordOK := fun (y : Array Nat) =>
    let yi := powA y (my - 1)
    ws.all fun (wd, o) =>
      let v := wd.foldr (fun l acc => comp (if l == 0 then r else if l == 1 then y
        else if l == 2 then xi else yi) acc) (idA n)
      o == 0 || orderA v == o
  let cs := counts2 L (idA n) fun y => orderA y == my && wordOK y
  let nE := lit n
  let wE := lit w
  let fE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntWord2F)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE,
      mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      lit L.size, lit mx, lit my, mkConst wsN, mkConst RN]
  withSync (emitCounts2 pre.getId Q fE cs)
