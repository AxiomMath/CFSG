module

public import Certificates.Data.Kernel.SporSch.ClsAll
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Kernel.SporSch.J1.GenPt
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.SporSch.J1.GenPt

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG in
elab "#kss_ptcntn " pre:ident qq:ident nn:num ww:num sId:ident bId:ident mxN:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let mx := mxN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let L := levelsOf n S base
  let nb := L.size
  let c0 := L[0]!.size
  let rest := (L.toList.drop 1).foldl (fun a T => a * T.size) 1
  let cs := (List.range c0).map fun k0 =>
    ((List.range rest).filter fun r => orderA (elemOf L n (k0 * rest + r)) == mx).length
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let RE := mkApp (mkConst ``List.nil [0]) natT
  let blk := 64
  let nbk := (cs.length + blk - 1) / blk
  let cs := (List.range nbk).map fun i => ((cs.drop (i * blk)).take blk).foldl (· + ·) 0
  let stmt := fun (kE : Expr) => mkAppN (mkConst ``CFSG.KS.SporSch.MOC.cntJB)
    #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit nb, lit mx, lit 0, lit 0, lit 0,
      mkConst (Q ++ `LR), mkConst (Q ++ `TR), RE, mulE kE (lit blk), lit blk]
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

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG in
elab "#kss_clsall " pre:ident qq:ident nn:num ww:num sId:ident bId:ident ngN:num mxN:num
    zId:ident : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let ng := ngN.getNat
  let mx := mxN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let Zarr ← evalArr zId
  let L := levelsOf n S base
  let nb := L.size
  let N := L.foldl (fun a T => a * T.size) 1
  let G := (S.toList.take ng).toArray
  let GI := G.map invA
  let isO := (Array.range N).map fun j => orderA (elemOf L n j) == mx
  let mut cls : Array Nat := Array.replicate N N
  let mut lists : Array (Array Nat) := #[]
  let mut pars : Array (Array Nat) := #[]
  let mut labs : Array (Array Nat) := #[]
  let mut deps : Array (Array Nat) := #[]
  for j0 in [0:N] do
    if isO[j0]! && cls[j0]! == N then
      let ci := lists.size
      cls := cls.set! j0 ci
      let mut bl : Array Nat := #[j0]
      let mut par : Array Nat := #[0]
      let mut lab : Array Nat := #[0]
      let mut dep : Array Nat := #[0]
      let mut h := 0
      while h < bl.size do
        let x := elemOf L n bl[h]!
        for l in [0:ng] do
          let jz := indexOf L base (comp G[l]! (comp x GI[l]!))
          if cls[jz]! == N then
            cls := cls.set! jz ci
            bl := bl.push jz
            par := par.push h
            lab := lab.push l
            dep := dep.push (dep[h]! + 1)
        h := h + 1
      lists := lists.push bl
      pars := pars.push par
      labs := labs.push lab
      deps := deps.push dep
  let mut O : Array Nat := #[0]
  let mut E : Array Nat := #[]
  let mut CL : Array Nat := #[]
  let mut PA : Array Nat := #[]
  let mut LB : Array Nat := #[]
  let mut DP : Array Nat := #[]
  let mut posOf : Std.HashMap Nat Nat := {}
  for ci in [0:lists.size] do
    let bl := lists[ci]!
    let ord := (Array.range bl.size).qsort fun a b => bl[a]! < bl[b]!
    let lo := E.size
    let mut pos := Array.replicate bl.size 0
    for k in [0:ord.size] do
      pos := pos.set! ord[k]! k
    for k in [0:ord.size] do
      let i := ord[k]!
      E := E.push bl[i]!
      CL := CL.push ci
      PA := PA.push (lo + pos[(pars[ci]!)[i]!]!)
      LB := LB.push (labs[ci]!)[i]!
      DP := DP.push (deps[ci]!)[i]!
      posOf := posOf.insert bl[i]! (lo + k)
    O := O.push E.size
  let K := E.size
  let IX := (Array.range (K * ng)).map fun t =>
    let k := t / ng
    let l := t % ng
    posOf.getD (indexOf L base (comp G[l]! (comp (elemOf L n E[k]!) GI[l]!))) 0
  let zp := posOf.getD (indexOf L base Zarr) K
  let nbk := (K + 63) / 64
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  withSync do
    addTree (P ++ `E) E
    addTree (P ++ `CL) CL
    addTree (P ++ `O) O
    addTree (P ++ `IX) IX
    addTree (P ++ `PA) PA
    addTree (P ++ `LB) LB
    addTree (P ++ `DP) DP
    addDef (P ++ `K) natT (lit K)
    addDef (P ++ `ncl) natT (lit lists.size)
    addDef (P ++ `zp) natT (lit zp)
    addDef (P ++ `Z) natT (lit (pack w Zarr))
    addDef (P ++ `nbk) natT (lit nbk)
    addDef (P ++ `N) natT (lit N)
    let ordE := mkApp2 (mkConst ``CFSG.KS.SporSch.MOC.ordK) (mkConst (Q ++ `LR)) (lit nb)
    let hNn := P ++ `hN
    let hNT := mkApp3 (mkConst ``Eq [1]) natT ordE (mkConst (P ++ `N))
    let hNV := mkApp2 (mkConst ``Eq.refl [1]) natT ordE
    CFSG.KC.addThmDecl <| { name := hNn, levelParams := [], type := hNT, value := hNV }
    let hdT := isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MOC.clsGHdK)
      #[nE, wE, mE, nwE, lit nb, mkConst (Q ++ `LR), mkConst (Q ++ `TR), mkConst (P ++ `E),
        mkConst (P ++ `O), mkConst (P ++ `K), mkConst (P ++ `ncl), mkConst (P ++ `zp),
        mkConst (P ++ `Z)])
    CFSG.KC.addThmDecl <| { name := P ++ `hd, levelParams := [], type := hdT, value := reflBoolTrue }
    let elemF := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.clsGK)
      #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit nb,
        mkConst (P ++ `N), lit ng,
        lit mx, mkConst (Q ++ `S), mkConst (Q ++ `SI), mkConst (Q ++ `LR), mkConst (Q ++ `TR),
        mkConst (P ++ `E), mkConst (P ++ `CL), mkConst (P ++ `O), mkConst (P ++ `IX),
        mkConst (P ++ `PA), mkConst (P ++ `LB), mkConst (P ++ `DP), mkConst (P ++ `K),
        mkConst (P ++ `ncl)]
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
