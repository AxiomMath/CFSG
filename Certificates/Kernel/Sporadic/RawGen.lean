module

public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.Kernel.Spor.Text
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGen

open CFSG.KC.Tab

meta def mulE (a b : Expr) : Expr :=
  mkAppN (mkConst ``HMul.hMul [0, 0, 0])
    #[natT, natT, natT, mkApp2 (mkConst ``instHMul [0]) natT (mkConst ``instMulNat), a, b]

meta def isTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def pack (w : Nat) (a : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:a.size] do
    acc := (acc <<< w) ||| a[a.size - 1 - i]!
  return acc

meta def inv (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

meta def comp (n : Nat) (t u : Array Nat) : Array Nat := Array.ofFn (n := n) fun i => t[u[i.val]!]!

meta def addTree (F : Name) (vs : Array Nat) : CoreM Unit := do
  let cnt := max vs.size 1
  let h := Nat.log2 (2 * cnt - 1)
  addDef (F ++ `Z) natT (lit 0)
  for k in [0:vs.size] do
    addDef (F ++ Name.mkSimple s!"L{k}") natT (lit vs[k]!)
  let leaf := fun k => constFn (if k < vs.size then mkConst (F ++ Name.mkSimple s!"L{k}")
    else mkConst (F ++ `Z))
  addDef F fnT (table leaf (1 <<< h) 0)

meta def forallChain (P : Expr) (k : Nat) (thm : Nat → Expr) : Expr := Id.run do
  let mut pf := mkApp (mkConst ``CFSG.KS.Raw.forall_lt_zero) P
  for s in [0:k] do
    pf := mkAppN (mkConst ``CFSG.KS.Raw.forall_lt_succ) #[P, lit s, pf, thm s]
  return pf

meta def addThm (nm : Name) (ty val : Expr) : CoreM Unit := do
  let val := if (← getOptions).getBool `debug.proofAsSorry && (← getEnv).contains ``sorryAx then
    mkApp2 (mkConst ``sorryAx [levelZero]) ty (mkConst ``Bool.false) else val
  addDecl <| .thmDecl { name := nm, levelParams := [], type := ty, value := val }

end CFSG.KS.RawGen

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_rawchain " pre:ident nn:num ww:num ch:num sId:ident bId:ident ko:num dId:ident :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
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
  let mut trs : Array Nat := #[]
  let mut tris : Array Nat := #[]
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
    for k in [0:c] do
      trs := trs.push (pack w tr[k]!)
      tris := tris.push (pack w (inv n tr[k]!))
  let BP := pack w base
  let NS := (n + CH - 1) / CH
  let natE := natT
  let fnE := fnT
  let _ := fnE
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
    addThm (P ++ `head) headT reflBoolTrue
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let lvT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.levelK)
      #[nE, wE, mE, nwE, pmE, idE, c `S, c `SI, c `TR, c `TRI, kSE,
        mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE], stepsE iE, mkApp (c `LR) iE])
    for i in [0:nb] do
      let nm := P ++ Name.mkSimple s!"lv{i}"
      addThm nm (lvT (lit i)) reflBoolTrue
    let lvP := mkLambda `i .default natE (lvT (mkBVar 0))
    let hlV := forallChain lvP nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK) #[nE, wE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, nbE, c `BP]
    addThm (P ++ `hl) hlT hlV
    if CH == 0 then return
    let schT := fun (iE sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
        mulE sE (lit CH), lit CH])
    for i in [0:nb] do
      for s in [0:NS] do
        let nm := P ++ Name.mkSimple s!"sch{i}_{s}"
        addThm nm (schT (lit i) (lit s)) reflBoolTrue
    let innerP := fun (iE : Expr) => mkLambda `s .default natE (schT iE (mkBVar 0))
    let outerBody := fun (iE : Expr) =>
      mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
        (schT (iE.liftLooseBVars 0 2) (mkBVar 1)))
    let outerP := mkLambda `i .default natE (outerBody (mkBVar 0))
    let hsV := forallChain outerP nb fun i =>
      forallChain (innerP (lit i)) NS fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
    let hsT := mkForall `i .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, nbE])
      (outerBody (mkBVar 1)))
    addThm (P ++ `hs) hsT hsV
    addDef (P ++ `NS) natE (lit NS)

open CFSG.KC.Tab in
elab "#ks_chars " pre:ident sId:ident : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let env ← getEnv
  let s ← match (env.find? sN).bind ConstantInfo.value? with
    | some (.lit (.strVal s)) => pure s
    | _ => liftTermElabM <| unsafe evalConst String sN
  let charE : Expr := mkConst ``Char
  let mk (ch : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
  let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charE (mk ch) acc)
    (mkApp (mkConst ``List.nil [0]) charE)
  let lty := mkApp (mkConst ``List [0]) charE
  let strE := mkConst ``String
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `chars) lty lst
    let ty := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN)
      (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    let pf := mkApp2 (mkConst ``Eq.refl [1]) strE (mkConst sN)
    let nEq := P ++ `eq
    CFSG.KS.RawGen.addThm nEq ty pf

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_hexlines " pre:ident sId:ident wdN:num nN:num wN:num : command => do
  let P := pre.getId
  let wd := wdN.getNat
  let n := nN.getNat
  let w := wN.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let hexv := fun (c : Char) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let ls := (s.splitOn "\n").filter (· ≠ "")
  let vals := ls.toArray.map fun l =>
    let cs := l.toList.toArray
    pack w (Array.ofFn (n := n) fun i => (List.range wd).foldl (fun acc t => acc * 16 +
      hexv cs[wd * i.val + t]!) 0)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `L) vals
    addDef (P ++ `lines) natT (lit vals.size)
    let ty := isTrue (mkAppN (mkConst ``CFSG.KS.Text.hexBind)
      #[mkConst (P ++ `chars), lit wd, lit n, lit w, lit vals.size, lit 0, lit vals.size,
        mkConst (P ++ `L)])
    let nAll := P ++ `all
    addThm nAll ty reflBoolTrue

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_perm " pre:ident ww:num tId:ident : command => do
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let t ← liftTermElabM <| unsafe evalConst (Array Nat) tN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef pre.getId natT (lit (pack ww.getNat t))

end
