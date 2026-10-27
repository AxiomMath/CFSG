module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.MBTG

open CFSG.KS.SporSch.MOCG CFSG.KS.RawGen

meta def parseHint (n : Nat) (s : String) : Except String (Array (Array Nat × Nat)) := do
  let mut out := #[]
  for ln in s.splitOn "\n" do
    let ws := (ln.splitOn " ").filter (· ≠ "")
    if ws.isEmpty then continue
    let vs ← ws.mapM fun t => match t.toNat? with
      | some v => pure v
      | none => throw s!"parseHint: bad token {t}"
    if vs.length != n + 1 then throw s!"parseHint: line of {vs.length} entries"
    out := out.push ((vs.take n).toArray, vs.getLast!)
  return out

meta def evalStr (id : Ident) : CommandElabM String := do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM <| unsafe evalConst String nm

meta def unpackA (n w c : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => (c >>> (w * i.val)) % (2 ^ w)

meta def wordA (x y xi yi : Array Nat) (wd : List Nat) : Array Nat :=
  wd.foldr (fun l acc => comp (if l = 0 then x else if l = 1 then y else if l = 2 then xi else yi)
    acc) (idA x.size)

meta def zTestA (mx my : Nat) (ws : List (List Nat × Nat)) (z x : Array Nat) : Bool :=
  let y := comp (powA x (mx - 1)) z
  orderA y == my &&
    ws.all fun p => p.2 == 0 || orderA (wordA x y (powA x (mx - 1)) (powA y (my - 1)) p.1) == p.2

meta def classCodes (w : Nat) (A B : Array Nat) (Rs : Array (Array Nat)) : Array (Array Nat) :=
  Id.run do
  let Ai := invA A
  let Bi := invA B
  let mut out := #[]
  for R in Rs do
    let mut bl : Array (Array Nat) := #[R]
    let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (pack w R)
    let mut h := 0
    while h < bl.size do
      let x := bl[h]!
      for z in [comp A (comp x Ai), comp B (comp x Bi)] do
        if !seen.contains (pack w z) then
          seen := seen.insert (pack w z)
          bl := bl.push z
      h := h + 1
    out := out.push ((bl.map (pack w)).qsort (· < ·))
  return out

end CFSG.KS.SporSch.MBTG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.MBTG in
elab "#kss_bt " pre:ident qq:ident nn:num ww:num kk:num hId:ident : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let k := kk.getNat
  let reps ← match parseHint n (← evalStr hId) with
    | .ok r => pure r
    | .error e => throwError e
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let XL := mkConst (P ++ `XL)
  let CL := mkConst (P ++ `CL)
  let getD := fun (l : Expr) (i : Expr) =>
    mkAppN (mkConst ``List.getD [0]) #[natT, l, i, lit 0]
  let ltE := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, a, b]
  let repT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MBT.repK)
    #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit k, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      mkConst (Q ++ `TRI), getD XL iE, getD CL iE])
  let distT := fun (jE iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MBT.distK)
    #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit k, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      mkConst (Q ++ `TRI), getD XL jE, getD XL iE])
  let len := reps.size
  let rN := fun (i : Nat) => P ++ Name.mkSimple s!"r{i}"
  let dN := fun (i j : Nat) => P ++ Name.mkSimple s!"d{i}_{j}"
  withSync do
    addDef (P ++ `XL) listT (listE (reps.map fun p => pack w p.1).toList)
    addDef (P ++ `CL) listT (listE (reps.map fun p => p.2).toList)
    for i in [0:len] do
      let nm := P ++ Name.mkSimple s!"r{i}"
      addThm nm (repT (lit i)) reflBoolTrue
    let pR := mkLambda `i .default natT (repT (mkBVar 0))
    let hrT := mkForall `i .default natT (mkForall `h .default (ltE (mkBVar 0) (lit len))
      (repT (mkBVar 1)))
    let hrV := forallChain pR len fun i => mkConst (rN i)
    addThm (P ++ `hr) hrT hrV
    for i in [0:len] do
      for j in [0:i] do
        let nm := P ++ Name.mkSimple s!"d{i}_{j}"
        addThm nm (distT (lit j) (lit i)) reflBoolTrue
    let inner := fun (iE : Expr) => mkForall `j .default natT (mkForall `h .default
      (ltE (mkBVar 0) (iE.liftLooseBVars 0 1)) (distT (mkBVar 1) (iE.liftLooseBVars 0 2)))
    let pD := mkLambda `i .default natT (inner (mkBVar 0))
    let hdT := mkForall `i .default natT (mkForall `h .default (ltE (mkBVar 0) (lit len))
      (inner (mkBVar 1)))
    let hdV := forallChain pD len fun i =>
      forallChain (mkLambda `j .default natT (distT (mkBVar 0) (lit i))) i fun j => mkConst (dN i j)
    addThm (P ++ `hd) hdT hdV
    let NE := mkApp2 (mkConst ``CFSG.KS.SporSch.MOC.ordK) (mkConst (Q ++ `LR)) (lit k)
    let sumE := mkApp (mkConst ``Nat.succ) (mkAppN (mkConst ``CFSG.KS.SporSch.MBT.sumAllK)
      #[NE, CL, mkApp2 (mkConst ``List.length [0]) natT XL])
    let hs0T := isTrue (mkApp2 (mkConst ``Nat.beq) sumE NE)
    addThm (P ++ `hs0) hs0T reflBoolTrue
    let hsT := mkApp3 (mkConst ``Eq [1]) natT sumE NE
    let hsV := mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) sumE NE (mkConst (P ++ `hs0))
    addThm (P ++ `hs) hsT hsV


open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.MBTG in
elab "#kss_zscan " pre:ident bt:ident ck:ident nn:num ww:num hId:ident aId:ident
    bbId:ident rId:ident wsId:ident mxN:num myN:num rN:num : command => do
  let P := pre.getId
  let BT := bt.getId
  let CK := ck.getId
  let n := nn.getNat
  let w := ww.getNat
  let mx := mxN.getNat
  let my := myN.getNat
  let r := rN.getNat
  let A ← evalArr aId
  let B ← evalArr bbId
  let Rs ← evalArrs rId
  let wsN ← liftCoreM <| realizeGlobalConstNoOverload wsId
  let ws ← liftTermElabM <| unsafe evalConst (List (List Nat × Nat)) wsN
  let reps ← match parseHint n (← evalStr hId) with
    | .ok r => pure r
    | .error e => throwError e
  let cls := classCodes w A B Rs
  let SC : Array (Array (Array Nat)) := reps.map fun p =>
    if orderA p.1 != r then #[] else cls.map fun codes =>
      (Array.range ((codes.size + 255) / 256)).map fun b =>
        ((List.range 256).filter fun l => b * 256 + l < codes.size &&
          zTestA mx my ws p.1 (unpackA n w codes[b * 256 + l]!)).length
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let idnE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
  let listT2 := mkApp (mkConst ``List [0]) listT
  let listT3 := mkApp (mkConst ``List [0]) listT2
  let consE := fun (ty h t : Expr) => mkApp3 (mkConst ``List.cons [0]) ty h t
  let nilE := fun (ty : Expr) => mkApp (mkConst ``List.nil [0]) ty
  let l2 := fun (a : Array (Array Nat)) =>
    a.foldr (fun x acc => consE listT (listE x.toList) acc) (nilE listT)
  let l3 := SC.foldr (fun x acc => consE listT2 (l2 x) acc) (nilE listT2)
  let dT := mkConst ``CFSG.KS.SporSch.MOC.ClsD
  let getN := fun (l : Expr) (i : Expr) => mkAppN (mkConst ``List.getD [0]) #[natT, l, i, lit 0]
  let XL := mkConst (BT ++ `XL)
  let SCc := mkConst (P ++ `SC)
  let entry := fun (i j bE : Expr) => getN (mkAppN (mkConst ``List.getD [0])
    #[listT, mkAppN (mkConst ``List.getD [0]) #[listT2, SCc, i, nilE listT], j, nilE natT]) bE
  let cntE := fun (i j bE : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.MBT.cntZK)
    #[nE, wE, mE, idnE, lit mx, lit my, mkConst wsN, getN XL i,
      mkAppN (mkConst ``List.getD [0]) #[dT, mkConst CK, j, mkConst ``CFSG.KS.SporSch.MOC.clsD0],
      mulE bE (lit 256), lit 256]
  let ltE := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, a, b]
  let cN := fun (i j b : Nat) => P ++ Name.mkSimple s!"c{i}_{j}_{b}"
  let hN := fun (i j : Nat) => P ++ Name.mkSimple s!"h{i}_{j}"
  let oN := fun (i : Nat) => P ++ Name.mkSimple s!"n{i}"
  withSync do
    addDef (P ++ `SC) listT3 l3
    for i in [0:reps.size] do
      if SC[i]!.size == 0 then
        let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp2 (mkConst ``Nat.beq)
          (mkAppN (mkConst ``CFSG.KS.M11.ordC) #[nE, wE, mE, getN XL (lit i)]) (lit r))
          (mkConst ``Bool.false)
        let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false)
        addThm (oN i) ty pf
      else
        for j in [0:SC[i]!.size] do
          let bs := (SC[i]!)[j]!
          for b in [0:bs.size] do
            let ty := isTrue (mkApp2 (mkConst ``Nat.beq) (cntE (lit i) (lit j) (lit b))
              (lit bs[b]!))
            addThm (cN i j b) ty reflBoolTrue
          let eqT := fun (bE : Expr) => mkApp3 (mkConst ``Eq [1]) natT (cntE (lit i) (lit j) bE)
            (entry (lit i) (lit j) bE)
          let pE := mkLambda `b .default natT (eqT (mkBVar 0))
          let hV := forallChain pE bs.size fun b =>
            mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) (cntE (lit i) (lit j) (lit b)) (lit bs[b]!)
              (mkConst (cN i j b))
          let hT := mkForall `b .default natT (mkForall `h .default (ltE (mkBVar 0) (lit bs.size))
            (eqT (mkBVar 1)))
          addThm (hN i j) hT hV


open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.MBTG in
elab "#kss_oddB " pre:ident qq:ident nn:num ww:num sId:ident bId:ident moN:num lN:num :
    command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let mo := moN.getNat
  let L := lN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let Lv := levelsOf n S base
  let nb := Lv.size
  let E := prods Lv 0 (idA n)
  let N := E.size
  let NB := (N + L - 1) / L
  let idn := idA n
  let isId := fun (g : Array Nat) => g == idn
  let c1 := fun (x h : Array Nat) => comp x (comp h (comp x (invA h)))
  let codes := E.map fun x => Id.run do
    if isId x || !isId (powA x mo) then return 0
    for j in [0:N] do
      if !isId (powA (c1 x E[j]!) mo) then return 1 + j
    for j1 in [0:N] do
      for j2 in [0:N] do
        let h2 := E[j2]!
        if !isId (powA (comp (c1 x E[j1]!) (comp h2 (comp x (invA h2)))) mo) then
          return 1 + N + j1 * N + j2
    return 0
  let codes := (Array.range (NB * L)).map fun j => codes[j % N]!
  let nE := lit n
  let wE := lit w
  let blkT := fun (sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MOC.oddK)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE,
      mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE, mkConst (Q ++ `LR), mkConst (Q ++ `TR), lit nb,
      lit mo, mkConst P, mulE sE (lit L), lit L])
  let bN := fun (s : Nat) => P ++ Name.mkSimple s!"b{s}"
  withSync do
    addTree P codes
    addDef (P ++ `NB) natT (lit NB)
    for s in [0:NB] do
      addThm (bN s) (blkT (lit s)) reflBoolTrue
    let ltE := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, a, b]
    let hT := mkForall `s .default natT (mkForall `h .default (ltE (mkBVar 0) (lit NB))
      (blkT (mkBVar 1)))
    let hV := forallChain (mkLambda `s .default natT (blkT (mkBVar 0))) NB fun s => mkConst (bN s)
    addThm (P ++ `hb) hT hV

end
