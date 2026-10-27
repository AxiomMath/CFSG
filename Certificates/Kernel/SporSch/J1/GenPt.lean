module

public import Certificates.Data.Kernel.SporSch.J1Pt
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.JPG

open CFSG.KS.SporSch.MOCG

meta def elemOf (L : Array (Array (Array Nat))) (n j : Nat) : Array Nat := Id.run do
  let mut j := j
  let mut acc := idA n
  for d' in [0:L.size] do
    let d := L.size - 1 - d'
    let c := L[d]!.size
    acc := comp (L[d]!)[j % c]! acc
    j := j / c
  return acc

meta def indexOf (L : Array (Array (Array Nat))) (base : Array Nat) (g : Array Nat) : Nat :=
  Id.run do
  let mut h := g
  let mut j := 0
  for i in [0:L.size] do
    let T := L[i]!
    let b := base[i]!
    let mut k := 0
    for kk in [0:T.size] do
      if (T[kk]!)[b]! == h[b]! then
        k := kk
    j := j * T.size + k
    h := comp (invA T[k]!) h
  return j

meta def ordA' (g : Array Nat) : Nat := orderA g

end CFSG.KS.SporSch.JPG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG in
elab "#kss_ptcnt " pre:ident qq:ident nn:num ww:num sId:ident bId:ident mxN:num myN:num rN:num
    sN:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let mx := mxN.getNat
  let my := myN.getNat
  let r := rN.getNat
  let s := sN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let L := levelsOf n S base
  let nb := L.size
  let jR := indexOf L base S[0]!
  let R := elemOf L n jR
  let Rp := powA R (mx - 1)
  let _ := Rp
  if nb != 3 then throwError "#kss_ptcnt: the twin handles three levels"
  let iter := fun (f : Nat → Nat) (e x : Nat) => (List.range e).foldl (fun y _ => f y) x
  let fixB := fun (f : Nat → Nat) => base.all fun b => f b == b
  let ordB := fun (f : Nat → Nat) (e : Nat) => 0 < e && fixB (iter f e) &&
    (List.range e).all fun d => d == 0 || e % d != 0 || !fixB (iter f d)
  let Rf := fun (x : Nat) => R[x]!
  let cs := (List.range L[0]!.size).map fun k0 => Id.run do
    let t0 := (L[0]!)[k0]!
    let mut c := 0
    for t1 in L[1]! do
      for t2 in L[2]! do
        let f := fun (x : Nat) => t0[t1[t2[x]!]!]!
        if ordB f mx then c := c + 1
        else if ordB f my then
          c := c + 1048576
          let g1 := fun (x : Nat) => Rf (f x)
          let g2 := fun (x : Nat) => Rf (f (iter Rf (mx - 1) (iter f (my - 1) x)))
          if ordB g1 r && ordB g2 s then
            c := c + 1099511627776
    return c
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let RE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.elemT)
    #[nE, nwE, mkConst (Q ++ `LR), mkConst (Q ++ `TR), lit nb, lit jR]
  let blk := 64
  let nbk := (cs.length + blk - 1) / blk
  let csB := (List.range nbk).map fun i => ((cs.drop (i * blk)).take blk).foldl (· + ·) 0
  let cs := csB
  let stmt := fun (kE : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntJB)
    #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit nb, lit mx, lit my, lit r, lit s,
      mkConst (Q ++ `LR), mkConst (Q ++ `TR), RE, mulE kE (lit blk), lit blk]
  withSync do
    addDef (P ++ `CS) listT (listE cs)
    addDef (P ++ `jR) natT (lit jR)
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

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG in
elab "#kss_ptcls " pre:ident qq:ident nn:num ww:num sId:ident bId:ident : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let L := levelsOf n S base
  let nb := L.size
  let jR := indexOf L base S[0]!
  let N := L.foldl (fun a T => a * T.size) 1
  let A := S[0]!
  let B := S[1]!
  let Ai := invA A
  let Bi := invA B
  let mut bl : Array Nat := #[jR]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut dep : Array Nat := #[0]
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert jR 0
  let mut h := 0
  while h < bl.size do
    let x := elemOf L n bl[h]!
    for l in [0:2] do
      let z := if l == 0 then comp A (comp x Ai) else comp B (comp x Bi)
      let jz := indexOf L base z
      if !seen.contains jz then
        seen := seen.insert jz bl.size
        bl := bl.push jz
        par := par.push h
        lab := lab.push l
        dep := dep.push (dep[h]! + 1)
    h := h + 1
  let ord := (Array.range bl.size).qsort fun a b => bl[a]! < bl[b]!
  let mut pos := Array.replicate bl.size 0
  for k in [0:ord.size] do
    pos := pos.set! ord[k]! k
  let E := ord.map fun i => bl[i]!
  let conjIdx := fun (g gi : Array Nat) (i : Nat) =>
    pos[seen.getD (indexOf L base (comp g (comp (elemOf L n bl[i]!) gi))) 0]!
  let IA := ord.map fun i => conjIdx A Ai i
  let IB := ord.map fun i => conjIdx B Bi i
  let PA := ord.map fun i => pos[par[i]!]!
  let LB := ord.map fun i => lab[i]!
  let DP := ord.map fun i => dep[i]!
  let c := bl.size
  let nbk := (c + 63) / 64
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let _ := N
  withSync do
    addTree (P ++ `E) E
    addTree (P ++ `IA) IA
    addTree (P ++ `IB) IB
    addTree (P ++ `PA) PA
    addTree (P ++ `LB) LB
    addTree (P ++ `DP) DP
    addDef (P ++ `c) natT (lit c)
    addDef (P ++ `r) natT (lit pos[0]!)
    addDef (P ++ `nb) natT (lit nbk)
    addDef (P ++ `jR) natT (lit jR)
    let S0 := mkApp (mkConst (Q ++ `S)) (lit 0)
    let S1 := mkApp (mkConst (Q ++ `S)) (lit 1)
    let SI0 := mkApp (mkConst (Q ++ `SI)) (lit 0)
    let SI1 := mkApp (mkConst (Q ++ `SI)) (lit 1)
    let elemF := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.clsPtK)
      #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit nb,
        mkApp2 (mkConst ``CFSG.KS.SporSch.MOC.ordK) (mkConst (Q ++ `LR)) (lit nb),
        S0, SI0, S1, SI1, mkConst (Q ++ `LR), mkConst (Q ++ `TR), mkConst (P ++ `E),
        mkConst (P ++ `IA), mkConst (P ++ `IB), mkConst (P ++ `PA), mkConst (P ++ `LB),
        mkConst (P ++ `DP), mkConst (P ++ `c), mkConst (P ++ `r)]
    let blkT := fun (sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KC.Enum.allBlk)
      #[mulE sE (lit 64), elemF, lit 64])
    for s in [0:nbk] do
      let nm := P ++ Name.mkSimple s!"e{s}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := blkT (lit s), value := reflBoolTrue }
    let pE := mkLambda `s .default natT (blkT (mkBVar 0))
    let hbV := forallChain pE nbk fun s => mkConst (P ++ Name.mkSimple s!"e{s}")
    let hbT := mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit nbk])
      (blkT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `hb, levelParams := [], type := hbT, value := hbV }

end
