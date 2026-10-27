module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.SporSch.MatSchDefs
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

namespace CFSG.KS.MatSchGen

meta def addThmV (nm : Name) (ty v : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := v }

meta def addThm (nm : Name) (ty : Expr) : CoreM Unit := addThmV nm ty reflBoolTrue

meta def vm (d v M : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:d] do
    if v.testBit k then acc := acc ^^^ ((M >>> (d * k)) % (1 <<< d))
  return acc

meta def mm (d A B : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:d] do
    acc := acc ||| (vm d ((A >>> (d * k)) % (1 <<< d)) B <<< (d * k))
  return acc

meta def ident (d : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:d] do
    acc := acc ||| (1 <<< (d * k + k))
  return acc

meta def solve (d : Nat) (V p : Array Nat) : Nat := Id.run do
  let mut piv : Array (Nat × Nat) := Array.replicate d (0, 0)
  for i in [0:V.size] do
    let mut x := V[i]!
    let mut y := V[p[i]!]!
    let mut go := true
    for b' in [0:d] do
      let b := d - 1 - b'
      if go && x.testBit b then
        let (px, py) := piv[b]!
        if px == 0 then
          piv := piv.set! b (x, y)
          go := false
        else
          x := x ^^^ px
          y := y ^^^ py
  let mut M := 0
  for k in [0:d] do
    let mut x := 1 <<< k
    let mut y := 0
    for b' in [0:d] do
      let b := d - 1 - b'
      if x.testBit b then
        let (px, py) := piv[b]!
        x := x ^^^ px
        y := y ^^^ py
    M := M ||| (y <<< (d * k))
  return M

meta partial def keyTree (kv : Array (Nat × Nat)) (lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then CFSG.KC.Tab.constFn (CFSG.KC.Tab.lit (kv[lo]!).2)
  else
    let mid := (lo + hi) / 2
    CFSG.KC.Tab.node (keyTree kv lo mid) (keyTree kv mid hi) (kv[mid]!).1

end CFSG.KS.MatSchGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.MatSchGen in
elab "#ks_matsch " pre:ident nn:num ww:num dd:num ch:num lch:num lm:num sId:ident bId:ident
    ko:num dId:ident vId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let d := dd.getNat
  let CH := ch.getNat
  let LCH := lch.getNat
  let lim := lm.getNat
  let kO := ko.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let vN ← liftCoreM <| realizeGlobalConstNoOverload vId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let V ← liftTermElabM <| unsafe evalConst (Array Nat) vN
  let kS := S.size
  let nb := base.size
  let Sinv := S.map (inv n)
  let SMs := S.map (solve d V)
  let SMIs := Sinv.map (solve d V)
  let I := ident d
  for j in [0:kS] do
    unless mm d SMs[j]! SMIs[j]! == I do throwError "#ks_matsch: generator {j} is not linear"
  let letM := fun (l : Nat) => if l < kS then SMs[l]! else SMIs[l - kS]!
  let letMI := fun (l : Nat) => if l < kS then SMIs[l]! else SMs[l - kS]!
  let mut recs : Array Nat := #[]
  let mut cnts : Array Nat := #[]
  let mut sts : Array Nat := #[]
  let mut offs : Array Nat := #[]
  let mut tms : Array Nat := #[]
  let mut tims : Array Nat := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let letters := idx.toArray ++ (idx.map fun j => j + kS).toArray
    let mut T := letters.size
    for c in [0:letters.size] do
      T := T ||| (letters[c]! <<< (8 + 8 * c))
    sts := sts.push T
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut tm : Array Nat := #[I]
    let mut tim : Array Nat := #[I]
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
            tm := tm.push (mm d tm[h]! (letM letters[j]!))
            tim := tim.push (mm d (letMI letters[j]!) tim[h]!)
    let c := pts.size
    let pad := fun (a : Array Nat) => a ++ Array.replicate (n - a.size) 0
    let mut R := c
    R := R ||| (pack w (pad pts) <<< 16)
    R := R ||| (pack w pos <<< (16 + nw))
    R := R ||| (pack w (pad par) <<< (16 + 2 * nw))
    R := R ||| (pack 8 (pad lab) <<< (16 + 3 * nw))
    recs := recs.push R
    cnts := cnts.push c
    offs := offs.push tms.size
    tms := tms ++ tm
    tims := tims ++ tim
  let BP := pack w base
  let NL := (n + LCH - 1) / LCH
  let PV := pack d V
  let md := (1 <<< d) - 1
  let lanes := Id.run do
    let mut acc := 0
    for k in [0:d] do
      acc := acc ||| (1 <<< (d * k))
    return acc
  let kv := ((Array.range n).map fun i => (V[i]!, i)).qsort fun a b => a.1 < b.1
  let natE := natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) (Sinv.map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `ST) sts
    addTree (P ++ `SM) SMs
    addTree (P ++ `SMI) SMIs
    addTree (P ++ `TM) tms
    addTree (P ++ `TIM) tims
    addTree (P ++ `OF) offs
    addDef (P ++ `BP) natE (lit BP)
    addDef (P ++ `PV) natE (lit PV)
    addDef (P ++ `LK) fnT (keyTree kv 0 kv.size)
    let nE := lit n
    let wE := lit w
    let dE := lit d
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mulE nE wE
    let mdE := lit md
    let LE := lit lanes
    let IE := lit I
    let idE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let kSE := lit kS
    let nbE := lit nb
    let lt := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, a, b]
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let schP := fun (iE : Expr) => mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.MatSch.schMK)
      #[nE, wE, nwE, dE, mdE, LE, IE, c `PV, c `S, c `SI, c `SM, c `SMI, c `LK, c `LR, c `OF, c `TM,
        c `TIM, kSE, c `BP, nbE, iE, mkApp (c `ST) iE, mulE (mkBVar 0) (lit CH), lit CH]))
    let NSi := fun (i : Nat) => (cnts[i]! + CH - 1) / CH
    if lim > 0 then
      for s in [0:min lim (NSi 0)] do
        addThm (P ++ Name.mkSimple s!"sch0_{s}") (mkApp (schP (lit 0)) (lit s)).headBeta
      return
    let headT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, mkConst dN, nbE, c `BP])
    addThm (P ++ `head) headT
    let stT := isTrue (mkAppN (mkConst ``CFSG.KC.Enum.allN) #[nbE, mkLambda `l .default natE
      (mkAppN (mkConst ``Nat.beq) #[mkApp (c `ST) (mkBVar 0), stepsE (mkBVar 0)])])
    addThm (P ++ `st) stT
    let rootE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE]
    let lhT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvHdTK)
      #[nE, wE, mE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE])
    let slP := fun (iE : Expr) => mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlTK)
      #[nE, wE, mE, nwE, c `S, c `SI, kSE, stepsE iE, mkApp (c `LR) iE,
        mulE (mkBVar 0) (lit LCH), lit LCH]))
    let mut tlPf : Array Expr := #[]
    for i in [0:nb] do
      let iE := lit i
      let lhN := P ++ Name.mkSimple s!"lh{i}"
      addThm lhN (lhT iE)
      for s in [0:NL] do
        addThm (P ++ Name.mkSimple s!"ls{i}_{s}") (mkApp (slP iE) (lit s)).headBeta
      let hsV := forallChain (slP iE) NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
      let hNV := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) nE (mulE (lit NL) (lit LCH)))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      tlPf := tlPf.push (mkAppN (mkConst ``CFSG.KS.Raw.treeLv_of_sl)
        #[nE, wE, mE, nwE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE, lit NL, lit LCH,
          c `S, c `SI, mkConst lhN, hsV, hNV])
    let tlBody := fun (iE : Expr) => mkAppN (mkConst ``And) #[lhT iE,
      mkForall `k .default natE (mkForall `h .default (lt (mkBVar 0) nE)
        (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvPtTK) #[nE, wE, mE, nwE, c `S, c `SI, kSE,
          stepsE (iE.liftLooseBVars 0 2), mkApp (c `LR) (iE.liftLooseBVars 0 2),
          mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c `LR) (iE.liftLooseBVars 0 2)),
          mkApp (mkConst ``CFSG.KS.Raw.stCnt) (stepsE (iE.liftLooseBVars 0 2)), mkBVar 1])))]
    let tlV := forallChain (mkLambda `i .default natE (tlBody (mkBVar 0))) nb fun i => tlPf[i]!
    let tlT := mkAppN (mkConst ``CFSG.KS.Raw.TreeOK) #[nE, wE, c `S, c `SI, c `LR, kSE, nbE, c `BP]
    addThmV (P ++ `tl) tlT tlV
    let hstT := mkAppN (mkConst ``CFSG.KS.Raw.StepsOK) #[nE, wE, c `S, c `ST, kSE, nbE, c `BP]
    let hstV := mkAppN (mkConst ``CFSG.KS.Raw.stepsOK_of) #[nE, wE, c `S, c `ST, kSE, nbE, c `BP,
      mkConst (P ++ `st)]
    addThmV (P ++ `hst) hstT hstV
    addThm (P ++ `vec) (isTrue (mkAppN (mkConst ``CFSG.KS.MatSch.vecK) #[nE, dE, mdE, c `PV, c `LK]))
    let bindP := mkLambda `j .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.MatSch.bindK)
      #[nE, wE, dE, mdE, LE, IE, c `PV, mkApp (c `S) (mkBVar 0), mkApp (c `SM) (mkBVar 0),
        mkApp (c `SMI) (mkBVar 0)]))
    for j in [0:kS] do
      addThm (P ++ Name.mkSimple s!"bind{j}") (mkApp bindP (lit j)).headBeta
    addThmV (P ++ `bind) (mkForall `j .default natE (mkForall `h .default (lt (mkBVar 0) kSE)
        (mkApp bindP (mkBVar 1)).headBeta))
      (forallChain bindP kS fun j => mkConst (P ++ Name.mkSimple s!"bind{j}"))
    let trP := mkLambda `l .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.MatSch.trK)
      #[nE, wE, nwE, dE, mdE, LE, IE, c `SM, c `SMI, c `TM, c `TIM, kSE, mkApp (c `ST) (mkBVar 0),
        mkApp (c `LR) (mkBVar 0), mkApp (c `OF) (mkBVar 0)]))
    for l in [0:nb] do
      addThm (P ++ Name.mkSimple s!"tr{l}") (mkApp trP (lit l)).headBeta
    addThmV (P ++ `tr) (mkForall `l .default natE (mkForall `h .default (lt (mkBVar 0) nbE)
        (mkApp trP (mkBVar 1)).headBeta))
      (forallChain trP nb fun l => mkConst (P ++ Name.mkSimple s!"tr{l}"))
    let mut hsPf : Array Expr := #[]
    for i in [0:nb] do
      let iE := lit i
      for s in [0:NSi i] do
        addThm (P ++ Name.mkSimple s!"sch{i}_{s}") (mkApp (schP iE) (lit s)).headBeta
      let inner := forallChain (schP iE) (NSi i) fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
      let hc := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
          (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c `LR) iE)) (mulE (lit (NSi i)) (lit CH)))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      hsPf := hsPf.push (mkAppN (mkConst ``CFSG.KS.MatSch.sch_of_sl)
        #[nE, wE, nwE, dE, mdE, LE, IE, c `PV, c `S, c `SI, c `SM, c `SMI, c `LK, c `LR, c `OF,
          c `TM, c `TIM, kSE, c `BP, nbE, iE, mkApp (c `ST) iE, lit (NSi i), lit CH, hc, inner])
    let hsT := mkAppN (mkConst ``CFSG.KS.MatSch.SchMOK) #[nE, wE, nwE, dE, mdE, LE, IE, c `PV,
      c `S, c `SI, c `SM, c `SMI, c `LK, c `LR, c `OF, c `TM, c `TIM, c `ST, kSE, c `BP, nbE]
    let hsBody := fun (iE : Expr) => mkForall `h .default natE (mkForall `hh .default
      (lt (mkBVar 0) (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c `LR) (iE.liftLooseBVars 0 1))))
      (isTrue (mkAppN (mkConst ``CFSG.KS.MatSch.schMK) #[nE, wE, nwE, dE, mdE, LE, IE, c `PV,
        c `S, c `SI, c `SM, c `SMI, c `LK, c `LR, c `OF, c `TM, c `TIM, kSE, c `BP, nbE,
        iE.liftLooseBVars 0 2, mkApp (c `ST) (iE.liftLooseBVars 0 2), mkBVar 1, lit 1])))
    let hsV := forallChain (mkLambda `i .default natE (hsBody (mkBVar 0))) nb fun i => hsPf[i]!
    addThmV (P ++ `hs) hsT hsV
