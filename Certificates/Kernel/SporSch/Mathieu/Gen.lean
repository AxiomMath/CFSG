module

public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.Spor.MEnum
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.MOCG

open CFSG.KC.Tab CFSG.KS.RawGen

meta def comp (t u : Array Nat) : Array Nat := u.map fun i => t[i]!

meta def invA (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate t.size 0
  for i in [0:t.size] do
    r := r.set! t[i]! i
  return r

meta def idA (n : Nat) : Array Nat := Array.range n

meta def powA (t : Array Nat) (e : Nat) : Array Nat := Id.run do
  let mut r := idA t.size
  for _ in [0:e] do
    r := comp t r
  return r

meta def orderA (t : Array Nat) : Nat := Id.run do
  let mut o := 1
  for i in [0:t.size] do
    let mut c := 1
    let mut j := t[i]!
    while j != i do
      j := t[j]!
      c := c + 1
    o := Nat.lcm o c
  return o

meta def evalW (n : Nat) (S : Array (Array Nat)) (wd : List Int) : Array Nat :=
  wd.foldr (fun z acc =>
    let g := S[z.natAbs - 1]!
    comp (if 0 < z then g else invA g) acc) (idA n)

meta def strongOf (n : Nat) (gens : Array (Array Nat)) (words : List (List Int)) :
    Array (Array Nat) :=
  words.foldl (fun S wd => S.push (evalW n S wd)) gens

meta def levelsOf (n : Nat) (S : Array (Array Nat)) (base : Array Nat) :
    Array (Array (Array Nat)) := Id.run do
  let Sinv := S.map invA
  let mut out := #[]
  for i in [0:base.size] do
    let idx := (List.range S.size).filter fun j =>
      (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut tr : Array (Array Nat) := #[Array.range n]
    for h in [0:n] do
      if h < pts.size then
        let x := pts[h]!
        for j in [0:steps.size] do
          let s := steps[j]!
          let y := s[x]!
          if pos[y]! == n then
            pos := pos.set! y pts.size
            pts := pts.push y
            tr := tr.push (comp s tr[h]!)
    out := out.push tr
  return out

meta partial def prods (L : Array (Array (Array Nat))) (i : Nat) (g : Array Nat) :
    Array (Array Nat) :=
  if i == L.size then #[g]
  else L[i]!.foldl (fun acc t => acc ++ prods L (i + 1) (comp g t)) #[]

meta def listE (l : List Nat) : Expr :=
  l.foldr (fun k acc => mkApp3 (mkConst ``List.cons [0]) natT (lit k) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

meta def listT : Expr := mkApp (mkConst ``List [0]) natT

meta def pairE (β : Expr) (a b : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) natT β a b

meta def classE (R : Nat) (Bl P Lb S : List Nat) : Expr :=
  let t4 := mkApp2 (mkConst ``Prod [0, 0]) listT listT
  let t3 := mkApp2 (mkConst ``Prod [0, 0]) listT t4
  let t2 := mkApp2 (mkConst ``Prod [0, 0]) listT t3
  let t1 := mkApp2 (mkConst ``Prod [0, 0]) natT t2
  let t0 := mkApp2 (mkConst ``Prod [0, 0]) natT t1
  let d4 := mkApp4 (mkConst ``Prod.mk [0, 0]) listT listT (listE Lb) (listE S)
  let d3 := mkApp4 (mkConst ``Prod.mk [0, 0]) listT t4 (listE P) d4
  let d2 := mkApp4 (mkConst ``Prod.mk [0, 0]) listT t3 (listE Bl) d3
  pairE t0 (lit 0) (pairE t1 (lit 0) (pairE t2 (lit R) d2))

meta def classT : Expr := mkConst ``CFSG.KS.MEnum.ClassDatum

meta def evalArr (id : Ident) : CommandElabM (Array Nat) := do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM <| unsafe evalConst (Array Nat) nm

meta def evalArrs (id : Ident) : CommandElabM (Array (Array Nat)) := do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM <| unsafe evalConst (Array (Array Nat)) nm

meta def forallLt (P : Expr) (c : Nat) (thm : Nat → Expr) : Expr := forallChain P c thm

end CFSG.KS.SporSch.MOCG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_list " pre:ident cId:ident : command => do
  let C ← evalArr cId
  withSync do
    addDef pre.getId listT (listE C.toList)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_classes " pre:ident nn:num ww:num aId:ident bId:ident rId:ident : command => do
  let n := nn.getNat
  let w := ww.getNat
  let A ← evalArr aId
  let B ← evalArr bId
  let Rs ← evalArrs rId
  let Ai := invA A
  let Bi := invA B
  let cls := Rs.toList.map fun R => Id.run do
    let mut bl : Array (Array Nat) := #[R]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (pack w R)
    let mut h := 0
    while h < bl.size do
      let x := bl[h]!
      for l in [0:2] do
        let z := if l == 0 then comp A (comp x Ai) else comp B (comp x Bi)
        if !seen.contains (pack w z) then
          seen := seen.insert (pack w z)
          bl := bl.push z
          par := par.push h
          lab := lab.push l
      h := h + 1
    let S := (bl.map (pack w)).qsort (· < ·)
    return classE (pack w R) (bl.map (pack w)).toList par.toList lab.toList S.toList
  let _ := n
  let lst := cls.foldr (fun d acc => mkApp3 (mkConst ``List.cons [0]) classT d acc)
    (mkApp (mkConst ``List.nil [0]) classT)
  withSync do
    addDef pre.getId (mkApp (mkConst ``List [0]) classT) lst

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_cntord " pre:ident qq:ident nn:num ww:num sId:ident bId:ident GId:ident gId:ident
    ee:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let e := ee.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let g0 ← evalArr gId
  let GN ← liftCoreM <| realizeGlobalConstNoOverload GId
  let L := levelsOf n S base
  let nb := L.size
  let cs := (List.range L[0]!.size).map fun k0 =>
    ((prods L 1 (comp g0 (L[0]!)[k0]!)).filter fun g => orderA g == e).size
  let nE := lit n
  let wE := lit w
  let stmt := fun (kE : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntOrdK)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE, mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE,
      mkConst (Q ++ `LR), mkConst (Q ++ `TR), lit nb, mkConst GN, lit e, kE]
  withSync do
    addDef (P ++ `CS) listT (listE cs)
    for k0 in [0:cs.length] do
      let ty := isTrue (mkApp2 (mkConst ``Nat.beq) (stmt (lit k0)) (lit cs[k0]!))
      let nm := P ++ Name.mkSimple s!"c{k0}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
    let eqT := fun (kE : Expr) => mkApp3 (mkConst ``Eq [1]) natT (stmt kE)
      (mkAppN (mkConst ``List.getD [0]) #[natT, mkConst (P ++ `CS), kE, lit 0])
    let pE := mkLambda `k .default natT (eqT (mkBVar 0))
    let hcV := forallLt pE cs.length fun k0 =>
      mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) (stmt (lit k0)) (lit cs[k0]!)
        (mkConst (P ++ Name.mkSimple s!"c{k0}"))
    let hcT := mkForall `k .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit cs.length])
      (eqT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `hc, levelParams := [], type := hcT, value := hcV }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_cntword " pre:ident qq:ident nn:num ww:num sId:ident bId:ident mxN:num myN:num
    wsId:ident RId:ident rId:ident : command => do
  let P := pre.getId
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
  let nb := L.size
  let xi := powA r (mx - 1)
  let wordOK := fun (y : Array Nat) =>
    let yi := powA y (my - 1)
    ws.all fun (wd, o) =>
      let v := wd.foldr (fun l acc => comp (if l == 0 then r else if l == 1 then y
        else if l == 2 then xi else yi) acc) (idA n)
      o == 0 || orderA v == o
  let cs := (List.range L[0]!.size).map fun k0 =>
    ((prods L 1 (L[0]!)[k0]!).filter fun y => orderA y == my && wordOK y).size
  let nE := lit n
  let wE := lit w
  let stmt := fun (kE : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntWordK)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE, mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE,
      mkConst (Q ++ `LR), mkConst (Q ++ `TR), lit nb, lit mx, lit my, mkConst wsN, mkConst RN, kE]
  withSync do
    addDef (P ++ `CS) listT (listE cs)
    for k0 in [0:cs.length] do
      let ty := isTrue (mkApp2 (mkConst ``Nat.beq) (stmt (lit k0)) (lit cs[k0]!))
      let nm := P ++ Name.mkSimple s!"c{k0}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
    let eqT := fun (kE : Expr) => mkApp3 (mkConst ``Eq [1]) natT (stmt kE)
      (mkAppN (mkConst ``List.getD [0]) #[natT, mkConst (P ++ `CS), kE, lit 0])
    let pE := mkLambda `k .default natT (eqT (mkBVar 0))
    let hcV := forallLt pE cs.length fun k0 =>
      mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) (stmt (lit k0)) (lit cs[k0]!)
        (mkConst (P ++ Name.mkSimple s!"c{k0}"))
    let hcT := mkForall `k .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit cs.length])
      (eqT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `hc, levelParams := [], type := hcT, value := hcV }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_odd " pre:ident qq:ident nn:num ww:num sId:ident bId:ident moN:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let mo := moN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let L := levelsOf n S base
  let nb := L.size
  let E := prods L 0 (idA n)
  let N := E.size
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
  let nE := lit n
  let wE := lit w
  withSync do
    addTree P codes
    let ty := isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MOC.oddK)
      #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE, mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE,
        mkConst (Q ++ `LR), mkConst (Q ++ `TR), lit nb, lit mo, mkConst P, lit 0,
        mkApp2 (mkConst ``CFSG.KS.SporSch.MOC.ordK) (mkConst (Q ++ `LR)) (lit nb)])
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }

end
