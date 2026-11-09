module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.SchTriv
public import CFSG.Certificates.Kernel.Spor.RawSch4FSound
public import CFSG.Certificates.Kernel.Spor.RawSch4JSound
public import CFSG.Certificates.Kernel.Spor.RawSlPSound
public import CFSG.Certificates.Kernel.Spor.RawTabSlSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Mathlib.GroupTheory.Schreier

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_rawchain_sl4 " pre:ident nn:num ww:num ch:num lch:num lm:num sId:ident bId:ident
    ko:num dId:ident : command => do
  let P := pre.getId
  let env ← getEnv
  let wN? : Option Name := if env.contains (P ++ `subJ) && env.contains (P ++ `subW) then
    some (P ++ `subW) else none
  let J? : Option (Array Nat) ← if wN?.isSome then
      pure (some (← liftTermElabM <| unsafe evalConst (Array Nat) (P ++ `subJ)))
    else pure none
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let LCH := lch.getNat
  let lim := lm.getNat
  let kO := ko.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let kS := S.size
  let nb := base.size
  let Sinv := S.map (inv n)
  let mut recs : Array Nat := #[]
  let mut cnts : Array Nat := #[]
  let mut trs : Array Nat := #[]
  let mut tris : Array Nat := #[]
  let mut trLv : Array (Array (Array Nat)) := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
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
            par := par.push h
            lab := lab.push j
            tr := tr.push (comp n s tr[h]!)
    let off := trs.size
    let c := pts.size
    let pad := fun (a : Array Nat) => a ++ Array.replicate (n - a.size) 0
    let mut R := c
    R := R ||| (pack w (pad pts) <<< 16)
    R := R ||| (pack w pos <<< (16 + nw))
    R := R ||| (pack w (pad par) <<< (16 + 2 * nw))
    R := R ||| (pack 8 (pad lab) <<< (16 + 3 * nw))
    R := R ||| (off <<< (16 + 3 * nw + 8 * n))
    recs := recs.push R
    cnts := cnts.push c
    trLv := trLv.push tr
    for k in [0:c] do
      trs := trs.push (pack w tr[k]!)
      tris := tris.push (pack w (inv n tr[k]!))
  let BP := pack w base
  let NS := (n + CH - 1) / CH
  let NL := (n + LCH - 1) / LCH
  let natE := natT
  let i₀ := nb - 4
  let JJ := (J?.getD #[]) ++ (J?.getD #[])
  let TJ := (List.range JJ.size).foldl (fun acc k => acc ||| (JJ[k]! <<< (8 + 8 * k))) JJ.size
  let E := if nb ≥ 4 then cnts[i₀ + 2]! else 0
  let D := if nb ≥ 4 then cnts[i₀ + 3]! else 0
  let mut us : Array Nat := #[]
  if nb ≥ 4 then
    let t1 := trLv[i₀ + 1]!
    let t2 := trLv[i₀ + 2]!
    let t3 := trLv[i₀ + 3]!
    for a in [0:t1.size] do
      for b in [0:E] do
        for c in [0:D] do
          us := us.push (pack w (comp n t1[a]! (comp n t2[b]! t3[c]!)))
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) (Sinv.map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `TR) trs
    addTree (P ++ `TRI) tris
    addDef (P ++ `BP) natE (lit BP)
    let nE := lit n
    let wE := lit w
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mulE nE wE
    let pmE := mkApp (mkConst ``CFSG.KS.mask) nwE
    let idE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let kSE := lit kS
    let nbE := lit nb
    let headT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, mkConst dN, nbE, c `BP])
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let rootE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE]
    let sfTab := if J?.isSome then lit TJ else stepsE (lit i₀)
    let sfT := fun (sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.sch4F)
      #[nE, wE, mE, nwE, c `S, c `SI, c `LR, c `TR, c `TRI, c `U, kSE, c `BP, lit i₀,
        sfTab, lit E, lit D, mulE sE (lit CH), lit CH])
    let addU : CoreM Unit := do
      addTree (P ++ `U) us
      addDef (P ++ `E) natE (lit E)
      addDef (P ++ `D) natE (lit D)
      let utT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.utab4F)
        #[nE, wE, mE, nwE, c `LR, c `TR, c `U, lit i₀, lit E, lit D])
      let tru := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
      let hcOf := fun (l NU K : Nat) => mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
        (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c `LR) (lit l))) (mulE (lit NU) (lit K))) tru
      let UK := 4
      let NU := (cnts[i₀ + 2]! + UK - 1) / UK
      let usP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.ut4SlF)
        #[nE, wE, mE, nwE, c `LR, c `TR, c `U, lit i₀, lit E, lit D, mulE (mkBVar 0) (lit UK),
          lit UK]))
      for s in [0:NU] do
        addThm (P ++ Name.mkSimple s!"ut_{s}") (mkApp usP (lit s)).headBeta reflBoolTrue
      addThm (P ++ `ut) utT (mkAppN (mkConst ``CFSG.KS.Raw.utab4F_of_sl)
        #[nE, wE, mE, nwE, lit i₀, lit E, lit D, lit NU, lit UK, c `LR, c `TR, c `U,
          forallChain usP NU fun s => mkConst (P ++ Name.mkSimple s!"ut_{s}"),
          hcOf (i₀ + 2) NU UK])
      let ivT := isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.invTabK) kSE (stepsE (lit i₀)))
      addThm (P ++ `inv) ivT reflBoolTrue
      if let some wN := wN? then
        let g12T := fun (l : Nat) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lv12K)
          #[wE, mE, c `S, c `SI, kSE, c `BP, lit l, stepsE (lit (l + 1)), stepsE (lit (l + 2))])
        addThm (P ++ `g12) (g12T i₀) reflBoolTrue
        addThm (P ++ `g23) (g12T (i₀ + 1)) reflBoolTrue
        let tjsT := isTrue (mkApp2 (mkConst ``CFSG.KC.Enum.allN)
          (mkApp (mkConst ``CFSG.KS.Raw.stCnt) (lit TJ))
          (mkLambda `a .default natE (mkApp2 (mkConst ``Nat.blt)
            (mkApp2 (mkConst ``CFSG.KS.Raw.stAt) (lit TJ) (mkBVar 0)) kSE)))
        addThm (P ++ `tjs) tjsT reflBoolTrue
        addThm (P ++ `dup) (isTrue (mkApp (mkConst ``CFSG.KS.Raw.dupTabK) (lit TJ))) reflBoolTrue
        addThm (P ++ `inc) (isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.incK) (lit TJ) (lit TJ)))
          reflBoolTrue
        let wdT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.stwK)
          #[nE, wE, mE, idE, c `S, c `SI, kSE, stepsE (lit i₀), lit TJ, mkConst wN, lit 0])
        addThm (P ++ `wd) wdT reflBoolTrue
        return
      let vtT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.vtab4K)
        #[nE, wE, mE, nwE, idE, c `LR, c `TRI, c `U, c `BP, lit i₀, lit E, lit D])
      let VK := 2
      let NV := (cnts[i₀ + 1]! + VK - 1) / VK
      let vsP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.vt4SlF)
        #[nE, wE, mE, nwE, idE, c `LR, c `TRI, c `U, c `BP, lit i₀, lit E, lit D,
          mulE (mkBVar 0) (lit VK), lit VK]))
      for s in [0:NV] do
        addThm (P ++ Name.mkSimple s!"vt_{s}") (mkApp vsP (lit s)).headBeta reflBoolTrue
      addThm (P ++ `vt) vtT (mkAppN (mkConst ``CFSG.KS.Raw.vtab4K_of_sl)
        #[nE, wE, mE, nwE, idE, c `BP, lit i₀, lit E, lit D, lit NV, lit VK, c `LR, c `TRI, c `U,
          forallChain vsP NV fun s => mkConst (P ++ Name.mkSimple s!"vt_{s}"),
          hcOf (i₀ + 1) NV VK])
    if lim > 0 then
      if nb ≥ 4 then
        addU
        for s in [0:min lim ((cnts[i₀]! + CH - 1) / CH)] do
          let nm := P ++ Name.mkSimple s!"sf{s}"
          addThm nm (sfT (lit s)) reflBoolTrue
      return
    addThm (P ++ `head) headT reflBoolTrue
    let lvT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.levelK)
      #[nE, wE, mE, nwE, pmE, idE, c `S, c `SI, c `TR, c `TRI, kSE, rootE iE, stepsE iE,
        mkApp (c `LR) iE])
    for i in [0:nb] do
      let iE := lit i
      let lhT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvHdK)
        #[nE, wE, mE, nwE, idE, c `TR, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE])
      let lhN := P ++ Name.mkSimple s!"lh{i}"
      addThm lhN lhT reflBoolTrue
      let slP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlK)
        #[nE, wE, mE, nwE, c `S, c `SI, c `TR, c `TRI, kSE, stepsE iE, mkApp (c `LR) iE,
          mulE (mkBVar 0) (lit LCH), lit LCH]))
      for s in [0:NL] do
        let loE := mulE (lit s) (lit LCH)
        let pN := P ++ Name.mkSimple s!"lsP{i}_{s}"
        addThm pN (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlKP)
          #[nE, wE, mE, nwE, c `S, c `SI, c `TR, c `TRI, kSE, stepsE iE, mkApp (c `LR) iE, loE,
            lit LCH])) reflBoolTrue
        let v := mkAppN (mkConst ``CFSG.KS.Raw.lvSlK_of_P)
          #[nE, wE, c `S, c `SI, c `TR, c `TRI, kSE, stepsE iE, mkApp (c `LR) iE, loE, lit LCH,
            mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true), mkConst pN]
        let nm := P ++ Name.mkSimple s!"ls{i}_{s}"
        addThm nm (mkApp slP (lit s)).headBeta v
      let hsV := forallChain slP NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
      let hN := mkApp2 (mkConst ``Nat.le_of_ble_eq_true) nE (mulE (lit NL) (lit LCH))
      let hNV := mkApp hN (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      let v := mkAppN (mkConst ``CFSG.KS.Raw.levelK_of_sl)
        #[nE, wE, mE, nwE, pmE, idE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE, lit NL, lit LCH,
          c `S, c `SI, c `TR, c `TRI, mkConst lhN, hsV, hNV]
      addThm (P ++ Name.mkSimple s!"lv{i}") (lvT iE) v
    let schT := fun (iE sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
        mulE sE (lit CH), lit CH])
    let lvP := mkLambda `i .default natE (lvT (mkBVar 0))
    let hlV := forallChain lvP nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK) #[nE, wE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, nbE, c `BP]
    addThm (P ++ `hl) hlT hlV
    if CH == 0 then return
    let NSi := fun (i : Nat) => (cnts[i]! + CH - 1) / CH
    let hcE := fun (i : Nat) => mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
        (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c `LR) (lit i))) (mulE (lit (NSi i)) (lit CH)))
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    if nb ≥ 4 then
      addU
      for s in [0:NSi i₀] do
        let sfN := P ++ Name.mkSimple s!"sf{s}"
        addThm sfN (sfT (lit s)) reflBoolTrue
      let sfP := mkLambda `s .default natE (sfT (mkBVar 0))
      let faV := forallChain sfP (NSi i₀) fun s => mkConst (P ++ Name.mkSimple s!"sf{s}")
      let faT := mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit (NSi i₀)])
        (sfT (mkBVar 1)))
      addThm (P ++ `fall) faT faV
    let innerP := fun (iE : Expr) => mkLambda `s .default natE (schT iE (mkBVar 0))
    let chainAt := fun (i : Nat) =>
      forallChain (innerP (lit i)) (NSi i) fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
    let order := if nb ≥ 4 && wN?.isSome then
      (List.range (nb - (i₀ + 1))).map (· + (i₀ + 1)) ++ List.range (i₀ + 1) else List.range nb
    for i in order do
      for s in [0:NSi i] do
        let nm := P ++ Name.mkSimple s!"sch{i}_{s}"
        if let some wN := (if nb ≥ 4 && i == i₀ then wN? else none) then
          let v := mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_sch4JL)
            #[nE, wE, kSE, lit kO, c `BP, lit i, lit E, lit D, lit TJ, lit (NSi i),
              lit (NSi (i + 1)), lit (NSi (i + 2)), lit (NSi (i + 3)), lit CH,
              c `S, c `SI, c `LR, c `TR, c `TRI, c `U, mkConst dN, mkConst wN,
              reflBoolTrue, reflBoolTrue, reflBoolTrue, mkConst (P ++ `head), mkConst (P ++ `hl),
              mkConst (P ++ `inv), mkConst (P ++ `g12), mkConst (P ++ `g23), mkConst (P ++ `tjs),
              mkConst (P ++ `dup), mkConst (P ++ `inc), mkConst (P ++ `wd), mkConst (P ++ `ut),
              hcE i, mkConst (P ++ `fall), hcE (i + 1), chainAt (i + 1), hcE (i + 2),
              chainAt (i + 2), hcE (i + 3), chainAt (i + 3), mulE (lit s) (lit CH), lit CH]
          addThm nm (schT (lit i) (lit s)) v
        else if nb ≥ 4 && i == i₀ then
          let v := mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_sch4FL)
            #[nE, wE, kSE, lit kO, c `BP, lit i, lit E, lit D, lit (NSi i), lit CH,
              c `S, c `SI, c `LR, c `TR, c `TRI, c `U, mkConst dN, reflBoolTrue, reflBoolTrue,
              reflBoolTrue, mkConst (P ++ `head), mkConst (P ++ `hl), mkConst (P ++ `inv), mkConst (P ++ `ut),
              mkConst (P ++ `vt), hcE i, mkConst (P ++ `fall), mulE (lit s) (lit CH), lit CH]
          addThm nm (schT (lit i) (lit s)) v
        else
          addThm nm (schT (lit i) (lit s)) reflBoolTrue
    let outerBody := fun (iE : Expr) =>
      mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
        (schT (iE.liftLooseBVars 0 2) (mkBVar 1)))
    let outerP := mkLambda `i .default natE (outerBody (mkBVar 0))
    let hsV := forallChain outerP nb fun i =>
      let iE := lit i
      let hc := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) (mkApp (c `LR) iE |> fun e =>
          mkApp (mkConst ``CFSG.KS.Raw.rcnt) e) (mulE (lit (NSi i)) (lit CH)))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      let inner := forallChain (innerP iE) (NSi i) fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
      mkAppN (mkConst ``CFSG.KS.Raw.schK_slices)
        #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
          lit NS, lit (NSi i), lit CH, hc, inner]
    let hsT := mkForall `i .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, nbE])
      (outerBody (mkBVar 1)))
    addThm (P ++ `hs) hsT hsV
    addDef (P ++ `NS) natE (lit NS)
