module

public import Certificates.Data.Kernel.SporSch.J1Cent
public import CFSG.Certificates.Kernel.SporSch.ClassLabSound
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Kernel.SporSch.J1.GenPt
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.SporSch.KeyBfsSound
public import CFSG.Sporadic.Schreier.J1CountCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import Certificates.Kernel.SporSch.J1.GenPt

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.JCG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG

meta def bfsIdx (L : Array (Array (Array Nat))) (base : Array Nat) (n : Nat) (root : Array Nat)
    (steps : Array (Array Nat → Array Nat)) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let jR := indexOf L base root
  let mut J : Array Nat := #[jR]
  let mut PA : Array Nat := #[0]
  let mut LB : Array Nat := #[0]
  let mut POS : Array Nat := #[]
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert jR 0
  let mut h := 0
  while h < J.size do
    let x := elemOf L n J[h]!
    for l in [0:steps.size] do
      let jz := indexOf L base (steps[l]! x)
      match seen.get? jz with
      | some q => POS := POS.push q
      | none =>
        seen := seen.insert jz J.size
        POS := POS.push J.size
        J := J.push jz
        PA := PA.push h
        LB := LB.push l
    h := h + 1
  return (J, PA, LB, POS)

meta def sortW (J : Array Nat) : Array Nat × Array Nat := Id.run do
  let ord := (Array.range J.size).qsort fun a b => J[a]! < J[b]!
  let mut inv := Array.replicate J.size 0
  for k in [0:ord.size] do
    inv := inv.set! ord[k]! k
  return (ord, inv)

meta def addBlocks (P : Name) (f : Expr) (nbk : Nat) : CoreM Unit := do
  let blkT := fun (sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KC.Enum.allBlk)
    #[mulE sE (lit 64), f, lit 64])
  for s in [0:nbk] do
    let nm := P ++ Name.mkSimple s!"e{s}"
    CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := blkT (lit s), value := reflBoolTrue }
  let pE := mkLambda `s .default natT (blkT (mkBVar 0))
  let hbV := forallChain pE nbk fun s => mkConst (P ++ Name.mkSimple s!"e{s}")
  let hbT := mkForall `s .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit nbk])
    (blkT (mkBVar 1)))
  CFSG.KC.addThmDecl <| { name := P ++ `hb, levelParams := [], type := hbT, value := hbV }

meta def addBfs (P Q : Name) (n w nb N c cap : Nat) (stp : Expr) (ng : Nat)
    (J PA LB POS SRT SRI : Array Nat) : CoreM Unit := do
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  addTree (P ++ `J) J
  addTree (P ++ `PA) PA
  addTree (P ++ `LB) LB
  addTree (P ++ `POS) POS
  addTree (P ++ `SRT) SRT
  addTree (P ++ `SRI) SRI
  addDef (P ++ `c) natT (lit c)
  addDef (P ++ `jR) natT (lit J[0]!)
  let hdT := isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.J1C.bfsHdK)
    #[mkConst (P ++ `c), lit cap, mkConst (P ++ `jR), mkConst (P ++ `J), mkConst (P ++ `PA),
      mkConst (P ++ `LB)])
  CFSG.KC.addThmDecl <| { name := P ++ `hd, levelParams := [], type := hdT, value := reflBoolTrue }
  let f := mkAppN (mkConst ``CFSG.KS.SporSch.J1C.bfsPtG)
    #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit nb, lit N, mkConst (Q ++ `LR), mkConst (Q ++ `TR),
      stp, lit ng, mkConst (P ++ `c), mkConst (P ++ `J), mkConst (P ++ `PA), mkConst (P ++ `LB),
      mkConst (P ++ `POS), mkConst (P ++ `SRT), mkConst (P ++ `SRI)]
  addBlocks P f ((c + 63) / 64)

end CFSG.KS.SporSch.JCG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_packeq " pre:ident ww:num aId:ident e:term : command => do
  let P := pre.getId
  let w := ww.getNat
  let A ← evalArr aId
  let eE ← liftTermElabM do
    let e ← Term.elabTerm e (some natT)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  withSync do
    addDef P natT (lit (pack w A))
    let eqT := isTrue (mkApp2 (mkConst ``Nat.beq) (mkConst P) eE)
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := eqT, value := reflBoolTrue }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG CFSG.KS.SporSch.JCG in
elab "#kss_ptconj " pre:ident qq:ident nn:num ww:num sId:ident bId:ident capN:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let L := levelsOf n S base
  let N := L.foldl (fun a T => a * T.size) 1
  let A := S[0]!
  let B := S[1]!
  let Ai := invA A
  let Bi := invA B
  let (J, PA, LB, POS) := bfsIdx L base n A
    #[fun x => comp A (comp x Ai), fun x => comp B (comp x Bi)]
  let (SRT, SRI) := sortW J
  let stp := mkAppN (mkConst ``CFSG.KS.SporSch.J1C.stpC)
    #[lit w, mkApp (mkConst ``CFSG.KS.mask) (lit w), mkConst (Q ++ `S), mkConst (Q ++ `SI)]
  withSync <| addBfs P Q n w L.size N J.size capN.getNat stp 2 J PA LB POS SRT SRI

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG CFSG.KS.SporSch.JCG in
elab "#kss_ptmul " pre:ident qq:ident nn:num ww:num sId:ident bId:ident dId:ident gId:ident
    capN:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let Dg ← evalArrs dId
  let L := levelsOf n S base
  let N := L.foldl (fun a T => a * T.size) 1
  let (J, PA, LB, POS) := bfsIdx L base n (idA n) (Dg.map fun d => fun x => comp x d)
  let (SRT, SRI) := sortW J
  let c := J.size
  let ng := Dg.size
  let mut PT : Array Nat := Array.replicate (c * c) 0
  for a in [0:c] do
    for b in [0:c] do
      let v := if b == 0 then a else POS[PT[a * c + PA[b]!]! * ng + LB[b]!]!
      PT := PT.set! (a * c + b) v
  let INV := (Array.range c).map fun a => ((List.range c).find? fun b => PT[a * c + b]! == 0).getD 0
  let cj := fun (a i : Nat) => PT[PT[a * c + i]! * c + INV[a]!]!
  let mut reps : Array Nat := #[]
  let mut lab : Array Nat := Array.replicate c 0
  let mut cjs : Array Nat := Array.replicate c 0
  let mut done : Array Bool := Array.replicate c false
  for i in [0:c] do
    if !done[i]! then
      let r := reps.size
      reps := reps.push i
      for cc in [0:c] do
        for k in [0:c] do
          if !done[k]! && cj cc i == k then
            done := done.set! k true
            lab := lab.set! k r
            cjs := cjs.set! k cc
  let stp := mkAppN (mkConst ``CFSG.KS.SporSch.J1C.stpM)
    #[lit w, mkApp (mkConst ``CFSG.KS.mask) (lit w), mkConst gId.getId]
  withSync do
    addBfs P Q n w L.size N c capN.getNat stp ng J PA LB POS SRT SRI
    addTree (P ++ `PT) PT
    addTree (P ++ `INV) INV
    let pf := mkAppN (mkConst ``CFSG.KS.SporSch.J1C.prodPtG)
      #[lit ng, mkConst (P ++ `c), mkConst (P ++ `PA), mkConst (P ++ `LB), mkConst (P ++ `POS),
        mkConst (P ++ `PT), mkConst (P ++ `INV)]
    let hpT := isTrue (mkAppN (mkConst ``CFSG.KC.Enum.allN) #[lit c, pf])
    CFSG.KC.addThmDecl <| { name := P ++ `hp, levelParams := [], type := hpT, value := reflBoolTrue }
    addDef (P ++ `REPS) listT (listE reps.toList)
    addDef (P ++ `LAB) listT (listE lab.toList)
    addDef (P ++ `CJ) listT (listE cjs.toList)
    let F := mkLambda `k .default natT (mkLambda `c' .default natT (mkLambda `i .default natT
      (mkApp2 (mkConst ``Nat.beq) (mkAppN (mkConst ``CFSG.KS.SporSch.J1C.cjK)
        #[mkConst (P ++ `c), mkConst (P ++ `PT), mkConst (P ++ `INV), mkBVar 1, mkBVar 0])
        (mkBVar 2))))
    let hlT := isTrue (mkAppN (mkConst ``CFSG.KS.ClassLab.labOK)
      #[mkApp2 (mkConst ``CFSG.KS.ClassLab.labR) (mkConst (P ++ `c)) F, mkConst (P ++ `REPS),
        mkConst (P ++ `LAB), mkConst (P ++ `CJ)])
    CFSG.KC.addThmDecl <| { name := P ++ `hl, levelParams := [], type := hlT, value := reflBoolTrue }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG CFSG.KS.SporSch.JCG in
elab "#kss_ptcent " pre:ident qq:ident nn:num ww:num sId:ident bId:ident moN:num : command => do
  let P := pre.getId
  let Q := qq.getId
  let n := nn.getNat
  let w := ww.getNat
  let mo := moN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let L := levelsOf n S base
  let nb := L.size
  let N := L.foldl (fun a T => a * T.size) 1
  let A := S[0]!
  let jR := indexOf L base A
  let atB := fun (j x : Nat) => Id.run do
    let mut y := x
    let mut jj := j
    for d' in [0:nb] do
      let d := nb - 1 - d'
      let T := L[d]!
      y := (T[jj % T.size]!)[y]!
      jj := jj / T.size
    return y
  let mut K : Array Nat := #[]
  for j in [0:N] do
    if base.all fun b => A[atB j b]! == atB j A[b]! then
      K := K.push j
  let X := K.map fun j => elemOf L n j
  let Xi := X.map invA
  let pos := fun (g : Array Nat) => ((List.range X.size).find? fun t => X[t]! == g).getD 0
  let moves := fun (f : Nat → Nat) => base.any fun b =>
    (List.range mo).foldl (fun y _ => f y) b != b
  let mut W1 : Array Nat := #[]
  let mut W2 : Array Nat := #[]
  let mut W3 : Array Nat := #[]
  let mut W4 : Array Nat := #[]
  for k in [0:X.size] do
    let x := X[k]!
    let isId := base.all fun b => x[b]! == b
    let pw := moves fun y => x[y]!
    if isId || pw then
      W1 := W1.push 0
      W2 := W2.push 0
      W3 := W3.push 0
      W4 := W4.push 0
    else
      let one := (List.range X.size).find? fun h =>
        moves fun y => x[(X[h]!)[x[(Xi[h]!)[y]!]!]!]!
      match one with
      | some h =>
        W1 := W1.push (h + 1)
        W2 := W2.push (pos Xi[h]!)
        W3 := W3.push 0
        W4 := W4.push 0
      | none =>
        let two := (List.range (X.size * X.size)).find? fun p =>
          let h := p / X.size
          let h2 := p % X.size
          moves fun y => x[(X[h]!)[x[(Xi[h]!)[(X[h2]!)[x[(Xi[h2]!)[y]!]!]!]!]!]!]!
        let p := two.getD 0
        W1 := W1.push (p / X.size + 1)
        W2 := W2.push (pos Xi[p / X.size]!)
        W3 := W3.push (p % X.size + 1)
        W4 := W4.push (pos Xi[p % X.size]!)
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let RE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.elemT)
    #[nE, nwE, mkConst (Q ++ `LR), mkConst (Q ++ `TR), lit nb, lit jR]
  withSync do
    addTree (P ++ `K) K
    addTree (P ++ `W1) W1
    addTree (P ++ `W2) W2
    addTree (P ++ `W3) W3
    addTree (P ++ `W4) W4
    addDef (P ++ `cK) natT (lit K.size)
    addDef (P ++ `jR) natT (lit jR)
    let f := mkAppN (mkConst ``CFSG.KS.SporSch.J1C.centPtK)
      #[nE, wE, mE, nwE, mkConst (Q ++ `BP), lit nb, lit N, lit mo, mkConst (Q ++ `LR),
        mkConst (Q ++ `TR), RE, mkConst (P ++ `K), mkConst (P ++ `W1), mkConst (P ++ `W2),
        mkConst (P ++ `W3), mkConst (P ++ `W4), mkConst (P ++ `cK)]
    addBlocks P f ((K.size + 63) / 64)

end
