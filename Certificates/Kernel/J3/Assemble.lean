module

public import Certificates.Kernel.HeRu.Assemble
meta import Certificates.Kernel.HeRu.Assemble
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.Certificates.LS

theorem runLab_congr {WT LB : Nat → Nat} {Hs x z : Nat} {l l' : List Nat} (h : l = l')
    (hp : Nat.beq (CFSG.KC.LabF.runLab WT LB Hs l x) z = true) :
    Nat.beq (CFSG.KC.LabF.runLab WT LB Hs l' x) z = true := h ▸ hp

end CFSG.Certificates.LS

namespace CFSG.Certificates.LS.Asm

meta partial def listElems (e : Expr) : Array Expr :=
  if e.isAppOfArity ``List.cons 3 then #[e.appFn!.appArg!] ++ listElems e.appArg! else #[]

meta def slices2 (env : Environment) (F : Name) : MetaM (Array (Name × Array Expr × Expr)) := do
  let mut out := #[]
  let mut d := 0
  while env.contains (F.appendAfter s!"{d}_0") do
    let mut k := 0
    while env.contains (F.appendAfter s!"{d}_{k}") do
      let n := F.appendAfter s!"{d}_{k}"
      let a ← lhsArgs env n
      out := out.push (n, a[0]!.getAppArgs, a[1]!)
      k := k + 1
    d := d + 1
  if out.isEmpty then throwError "no slice theorems {F}0_0, …"
  return out

end CFSG.Certificates.LS.Asm

open CFSG.Certificates.LS.Asm in
elab "#labF_ok2 " nm:ident p:ident nR:num nS:num labs:ident : command => do
  let P := p.getId
  let N := nm.getId
  liftTermElabM do
    let env ← getEnv
    let sW ← slices env (P ++ `sW)
    let sL ← slices2 env (P ++ `sL)
    let aW ← lhsArgs env (P ++ `sH0)
    let aI ← lhsArgs env (P ++ `sH1)
    let aC ← lhsArgs env (P ++ `sH3)
    let aH ← lhsArgs env (P ++ `sH6)
    let aY ← lhsArgs env (P ++ `sY0)
    let fF := sW[0]!.2.1
    let fL := sL[0]!.2.1
    let blk := fF[0]!
    let WT := fF[1]!
    let INV := fF[2]!
    let nC := fF[3]!
    let L := fF[4]!
    let LB := fL[1]!
    let Hs := fL[2]!
    let RT := aW[1]!
    let ST := aW[2]!
    let INV8 := aW[4]!
    let m := aW[5]!
    let nCa := aC[1]!
    let K := aH[2]!
    let nf := aY[3]!
    unless aW[0]! == WT && aW[3]! == INV && aW[6]! == Hs && aI[0]! == INV && aI[1]! == INV8 &&
      aI[2]! == L && aC[0]! == nC && aY[0]! == blk && aY[1]! == WT && aY[2]! == LB &&
      fL[0]! == WT && aH[0]! == WT && aH[1]! == m && aH[3]! == Hs do
      throwError "the theorems of {P} name different tables"
    for (n, a, _) in sW do
      unless a.extract 0 5 == fF.extract 0 5 do throwError "{n}: a slice of another loop"
    for (n, a, _) in sL do
      unless a.extract 0 3 == fL.extract 0 3 do throwError "{n}: a slice of another loop"
    let chW := sW.foldl (fun acc (_, a, _) => acc ++ listElems a[5]!) #[]
    let chL := sL.foldl (fun acc (_, a, _) => acc ++ listElems a[3]!) #[]
    unless chW == chL do throwError "the label loop runs over other chunks"
    let (Cs, S0, S1, pF) := joinTree ``CFSG.Certificates.LS.facts_join (fF.extract 0 5) 5 sW 0 sW.size
    let c := fun (s : Name) => mkConst (P ++ s)
    withOptions (Elab.async.set · false) do
      let mut perD : Array (Name × Array Expr × Expr) := #[]
      let mut pos := 0
      for d in [0:sW.size] do
        let Ld := sW[d]!.2.1[5]!
        let nd := (listElems Ld).size
        let mut cnt := 0
        let mut hi := pos
        while cnt < nd do
          cnt := cnt + (listElems sL[hi]!.2.1[3]!).size
          hi := hi + 1
        unless cnt == nd do throwError "label slices do not end with fact slice {d}"
        let (l, x, z, p) := joinTree ``CFSG.Certificates.LS.labF_join (fL.extract 0 3) 3 sL pos hi
        let stmt := fun (lst : Expr) => isTrue (mkApp2 (mkConst ``Nat.beq)
          (mkAppN (mkConst ``CFSG.KC.LabF.runLab) #[WT, LB, Hs, lst, x]) z)
        let listT := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
        let hEq := mkApp2 (mkConst ``Eq.refl [Level.one]) listT l
        let castP := mkAppN (mkConst ``CFSG.Certificates.LS.runLab_congr)
          #[WT, LB, Hs, x, z, l, Ld, hEq, p]
        let nd' := N ++ Name.mkSimple s!"lab{d}"
        CFSG.KC.addThmDecl <| { name := nd', levelParams := [], type := stmt Ld, value := castP }
        perD := perD.push (nd', #[WT, LB, Hs, Ld, x], z)
        pos := hi
      unless pos == sL.size do throwError "label slices past the last fact slice"
      let (_, X0, X1, pL) := joinTree ``CFSG.Certificates.LS.labF_join (fL.extract 0 3) 3 perD 0
        perD.size
      let nIds := N ++ `ids
      let type := isTrue (mkApp2 (mkConst ``Nat.beq)
        (mkAppN (mkConst ``CFSG.KC.LceSR.runIds) #[WT, m, Cs, lit 1]) (lit 1))
      CFSG.KC.addThmDecl <| { name := nIds, levelParams := [], type, value := reflBoolTrue }
      let nLabs ← realizeGlobalConstNoOverload labs
      let r := reflBoolTrue
      let nR := lit nR.getNat
      let nS := lit nS.getNat
      let nHints := N ++ `hints
      let type := isTrue (mkAppN (mkConst ``CFSG.KC.Bind.hintsOK) #[WT, m, nR, nS, Hs])
      CFSG.KC.addThmDecl <| { name := nHints, levelParams := [], type, value := r }
      let nNorm := N ++ `norm
      let type := isTrue (mkApp2 (mkConst ``CFSG.Certificates.LCE.relsNorm) RT nR)
      CFSG.KC.addThmDecl <| { name := nNorm, levelParams := [], type, value := r }
      let args := #[blk, WT, RT, ST, LB, INV, INV8, L, nC, nCa, nf, m, Hs, nR, nS, K, S0, S1,
        X0, X1, Cs]
      let pf := mkAppN (mkConst ``CFSG.Certificates.LS.LabF.labOk_intro) (args ++
        #[c `sH0, mkConst nHints, mkConst nNorm, c `sH1, c `sH3, r, r, r, r, r, r, c `sH6,
          mkConst nLabs, mkConst nIds, pF, pL])
      let type := isTrue (mkAppN (mkConst ``CFSG.Certificates.LS.LabF.labOk) args)
      CFSG.KC.addThmDecl <| { name := N, levelParams := [], type, value := pf }

end
