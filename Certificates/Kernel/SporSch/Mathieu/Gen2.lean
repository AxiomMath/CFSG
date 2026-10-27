module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Data.Kernel.SporSch.MathieuOC2
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.MOCG

open CFSG.KC.Tab CFSG.KS.RawGen

meta def emitCounts2 (P Q : Name) (fE : Expr) (cs : List (List Nat)) : CoreM Unit := do
  let lstT := mkApp (mkConst ``List [0]) listT
  let csE := cs.foldr (fun l acc => mkApp3 (mkConst ``List.cons [0]) listT (listE l) acc)
    (mkApp (mkConst ``List.nil [0]) listT)
  addDef (P ++ `CS) lstT csE
  let CSc := mkConst (P ++ `CS)
  let stmt := fun (a b : Expr) => mkApp2 fE a b
  for k0 in [0:cs.length] do
    let row := cs[k0]!
    for k1 in [0:row.length] do
      let ty := isTrue (mkApp2 (mkConst ``Nat.beq) (stmt (lit k0) (lit k1)) (lit row[k1]!))
      let nm := P ++ Name.mkSimple s!"c{k0}_{k1}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
  let getRow := fun (kE : Expr) =>
    mkAppN (mkConst ``List.getD [0]) #[listT, CSc, kE, mkApp (mkConst ``List.nil [0]) natT]
  let eqT := fun (a b : Expr) => mkApp3 (mkConst ``Eq [1]) natT (stmt a b)
    (mkAppN (mkConst ``List.getD [0]) #[natT, getRow a, b, lit 0])
  let LR := mkConst (Q ++ `LR)
  let cnt := fun (i : Nat) => mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp LR (lit i))
  let ltE := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, a, b]
  let innerAll := fun (a : Expr) => mkForall `k₁ .default natT (mkForall `h .default
    (ltE (mkBVar 0) (cnt 1)) (eqT (a.liftLooseBVars 0 2) (mkBVar 1)))
  let lenRow := fun (a : Expr) => mkApp3 (mkConst ``Eq [1]) natT
    (mkApp2 (mkConst ``List.length [0]) natT (getRow a)) (cnt 1)
  let rowP := fun (a : Expr) => mkApp2 (mkConst ``And) (lenRow a) (innerAll a)
  let rowProof := fun (k0 : Nat) =>
    let row := cs[k0]!
    let pE := mkLambda `k₁ .default natT (eqT (lit k0) (mkBVar 0))
    let inner := forallChain pE row.length fun k1 =>
      mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) (stmt (lit k0) (lit k1)) (lit row[k1]!)
        (mkConst (P ++ Name.mkSimple s!"c{k0}_{k1}"))
    mkAppN (mkConst ``And.intro) #[lenRow (lit k0), innerAll (lit k0),
      mkApp2 (mkConst ``Eq.refl [1]) natT (lit row.length), inner]
  let outerP := mkLambda `k₀ .default natT (rowP (mkBVar 0))
  let outer := forallChain outerP cs.length rowProof
  let lenT := mkApp3 (mkConst ``Eq [1]) natT (mkApp2 (mkConst ``List.length [0]) listT CSc) (cnt 0)
  let outerT := mkForall `k₀ .default natT (mkForall `h .default (ltE (mkBVar 0) (cnt 0))
    (rowP (mkBVar 1)))
  let ty := mkApp3 (mkConst ``CFSG.KS.SporSch.MOC.Counts2) LR CSc fE
  let val := mkAppN (mkConst ``And.intro) #[lenT, outerT,
    mkApp2 (mkConst ``Eq.refl [1]) natT (lit cs.length), outer]
  CFSG.KC.addThmDecl <| { name := P ++ `hc, levelParams := [], type := ty, value := val }

meta def counts2 (L : Array (Array (Array Nat))) (g0 : Array Nat) (p : Array Nat → Bool) :
    List (List Nat) :=
  let L0 := L[0]!
  let L1 := L[1]!
  (List.range L0.size).map fun k0 => (List.range L1.size).map fun k1 =>
    let t0 := L0[k0]!
    let t1 := L1[k1]!
    ((prods L 2 (comp (comp g0 t0) t1)).filter p).size

end CFSG.KS.SporSch.MOCG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_cntcomm " pre:ident qq:ident nn:num ww:num sId:ident bId:ident GId:ident gId:ident
    AId:ident aId:ident BId:ident bbId:ident : command => do
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let g0 ← evalArr gId
  let a ← evalArr aId
  let b ← evalArr bbId
  let GN ← liftCoreM <| realizeGlobalConstNoOverload GId
  let AN ← liftCoreM <| realizeGlobalConstNoOverload AId
  let BN ← liftCoreM <| realizeGlobalConstNoOverload BId
  let L := levelsOf n S base
  let cs := counts2 L g0 fun g => comp g a == comp a g && comp g b == comp b g
  let nE := lit n
  let wE := lit w
  let fE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntCommK)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE, mkConst (Q ++ `LR),
      mkConst (Q ++ `TR), lit L.size, mkConst GN, mkConst AN, mkConst BN]
  withSync (emitCounts2 pre.getId Q fE cs)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_cntord2 " pre:ident qq:ident nn:num ww:num sId:ident bId:ident GId:ident gId:ident
    ee:num : command => do
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let e := ee.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let g0 ← evalArr gId
  let GN ← liftCoreM <| realizeGlobalConstNoOverload GId
  let L := levelsOf n S base
  let cs := counts2 L g0 fun g => orderA g == e
  let nE := lit n
  let wE := lit w
  let fE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntOrd2K)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE,
      mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      lit L.size, mkConst GN, lit e]
  withSync (emitCounts2 pre.getId Q fE cs)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_cntword2 " pre:ident qq:ident nn:num ww:num sId:ident bId:ident mxN:num myN:num
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
  let fE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntWord2K)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE,
      mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      lit L.size, lit mx, lit my, mkConst wsN, mkConst RN]
  withSync (emitCounts2 pre.getId Q fE cs)

end
