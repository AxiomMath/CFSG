module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG in
elab "#kss_classes2 " pre:ident nn:num ww:num aId:ident bId:ident taId:ident tbId:ident rId:ident
    mxN:num capN:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let mx := mxN.getNat
  let cap := capN.getNat
  let A ← evalArr aId
  let B ← evalArr bId
  let Rs ← evalArrs rId
  let Ai := invA A
  let Bi := invA B
  let nE := lit n
  let wE := lit w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let taN ← liftCoreM <| realizeGlobalConstNoOverload taId
  let tbN ← liftCoreM <| realizeGlobalConstNoOverload tbId
  let packE := fun (l : Name) => mkApp2 (mkConst ``CFSG.KS.M11.packL) wE (mkConst l)
  let invE := fun (e : Expr) => mkAppN (mkConst ``CFSG.KS.pinvS) #[nE, wE, mE, e]
  let dT := mkConst ``CFSG.KS.SporSch.MOC.ClsD
  withSync do
    let mut ds : Array Expr := #[]
    let mut nbs : Array Nat := #[]
    for j in [0:Rs.size] do
      let R := Rs[j]!
      let mut bl : Array (Array Nat) := #[R]
      let mut par : Array Nat := #[0]
      let mut lab : Array Nat := #[0]
      let mut dep : Array Nat := #[0]
      let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (pack w R) 0
      let mut h := 0
      while h < bl.size do
        let x := bl[h]!
        for l in [0:2] do
          let z := if l == 0 then comp A (comp x Ai) else comp B (comp x Bi)
          if !seen.contains (pack w z) then
            seen := seen.insert (pack w z) bl.size
            bl := bl.push z
            par := par.push h
            lab := lab.push l
            dep := dep.push (dep[h]! + 1)
        h := h + 1
      let codes := bl.map (pack w)
      let ord := (Array.range bl.size).qsort fun a b => codes[a]! < codes[b]!
      let mut pos := Array.replicate bl.size 0
      for k in [0:ord.size] do
        pos := pos.set! ord[k]! k
      let ST := ord.map fun i => codes[i]!
      let IA := ord.map fun i => pos[seen.getD (pack w (comp A (comp bl[i]! Ai))) 0]!
      let IB := ord.map fun i => pos[seen.getD (pack w (comp B (comp bl[i]! Bi))) 0]!
      let PA := ord.map fun i => pos[par[i]!]!
      let LB := ord.map fun i => lab[i]!
      let DP := ord.map fun i => dep[i]!
      let base := P ++ Name.mkSimple s!"d{j}"
      addTree (base ++ `ST) ST
      addTree (base ++ `IA) IA
      addTree (base ++ `IB) IB
      addTree (base ++ `PA) PA
      addTree (base ++ `LB) LB
      addTree (base ++ `DP) DP
      let dE := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.ClsD.mk)
        #[lit (pack w R), lit bl.size, lit pos[0]!, mkConst (base ++ `ST), mkConst (base ++ `IA),
          mkConst (base ++ `IB), mkConst (base ++ `PA), mkConst (base ++ `LB), mkConst (base ++ `DP)]
      addDef base dT dE
      ds := ds.push (mkConst base)
      nbs := nbs.push ((bl.size + 255) / 256)
    let lst := ds.foldr (fun d acc => mkApp3 (mkConst ``List.cons [0]) dT d acc)
      (mkApp (mkConst ``List.nil [0]) dT)
    addDef P (mkApp (mkConst ``List [0]) dT) lst
    let getD := fun (j : Nat) => mkAppN (mkConst ``List.getD [0])
      #[dT, mkConst P, lit j, mkConst ``CFSG.KS.SporSch.MOC.clsD0]
    let A0 := packE taN
    let Ai0 := invE (packE taN)
    let B0 := packE tbN
    let Bi0 := invE (packE tbN)
    for j in [0:ds.size] do
      let hdT := isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.MOC.clsHdK) #[nE, wE, mE, lit mx, lit cap,
        getD j])
      let nm546 := P ++ Name.mkSimple s!"h{j}"
      CFSG.KC.addThmDecl <| { name := nm546, levelParams := [], type := hdT, value := reflBoolTrue }
      let elemF := mkAppN (mkConst ``CFSG.KS.SporSch.MOC.clsElemK)
        #[nE, wE, mE, nwE, A0, Ai0, B0, Bi0, getD j]
      let blkT := fun (sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KC.Enum.allBlk)
        #[mulE sE (lit 256), elemF, lit 256])
      for s in [0:nbs[j]!] do
        let nm := P ++ Name.mkSimple s!"e{j}_{s}"
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := blkT (lit s), value := reflBoolTrue }
      let pE := mkLambda `s .default natT (blkT (mkBVar 0))
      let hbV := forallChain pE nbs[j]! fun s => mkConst (P ++ Name.mkSimple s!"e{j}_{s}")
      let hbT := mkForall `s .default natT (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit nbs[j]!])
        (blkT (mkBVar 1)))
      let nm763 := P ++ Name.mkSimple s!"hb{j}"
      CFSG.KC.addThmDecl <| { name := nm763, levelParams := [], type := hbT, value := hbV }
      addDef (P ++ Name.mkSimple s!"nb{j}") natT (lit nbs[j]!)
      for i in [0:j] do
        let ty := isTrue (mkApp2 (mkConst ``CFSG.KS.SporSch.MOC.notInK) (getD i)
          (mkApp (mkConst ``CFSG.KS.SporSch.MOC.ClsD.R) (getD j)))
        let nm491 := P ++ Name.mkSimple s!"n{j}_{i}"
        CFSG.KC.addThmDecl <| { name := nm491, levelParams := [], type := ty, value := reflBoolTrue }

end
