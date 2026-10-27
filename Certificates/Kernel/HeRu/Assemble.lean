module

public import Certificates.Data.Kernel.LceSHeRu
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.Certificates.LS

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem runFacts_append (blk WT : Nat → Nat) (INV nC L : Nat) : ∀ (l1 l2 : List Nat) (x : Nat),
    runFacts blk WT INV nC L (List.append l1 l2) x =
      runFacts blk WT INV nC L l2 (runFacts blk WT INV nC L l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (runChunk blk WT INV nC L C x) (runFacts blk WT INV nC L (List.append l1 l2)) =
      runFacts blk WT INV nC L l2 (strictN (runChunk blk WT INV nC L C x) (runFacts blk WT INV nC L l1))
    rw [strictN_eq, strictN_eq]
    exact runFacts_append blk WT INV nC L l1 l2 _

theorem facts_join (blk WT : Nat → Nat) (INV nC L : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (runFacts blk WT INV nC L l1 x) y = true)
    (h2 : Nat.beq (runFacts blk WT INV nC L l2 y) z = true) :
    Nat.beq (runFacts blk WT INV nC L (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [runFacts_append, h1, h2]

theorem labF_append (WT LB : Nat → Nat) (Hs : Nat) : ∀ (l1 l2 : List Nat) (x : Nat),
    CFSG.KC.LabF.runLab WT LB Hs (List.append l1 l2) x =
      CFSG.KC.LabF.runLab WT LB Hs l2 (CFSG.KC.LabF.runLab WT LB Hs l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (CFSG.KC.LabF.labChunk WT LB Hs C x)
        (CFSG.KC.LabF.runLab WT LB Hs (List.append l1 l2)) =
      CFSG.KC.LabF.runLab WT LB Hs l2 (strictN (CFSG.KC.LabF.labChunk WT LB Hs C x)
        (CFSG.KC.LabF.runLab WT LB Hs l1))
    rw [strictN_eq, strictN_eq]
    exact labF_append WT LB Hs l1 l2 _

theorem labF_join (WT LB : Nat → Nat) (Hs : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (CFSG.KC.LabF.runLab WT LB Hs l1 x) y = true)
    (h2 : Nat.beq (CFSG.KC.LabF.runLab WT LB Hs l2 y) z = true) :
    Nat.beq (CFSG.KC.LabF.runLab WT LB Hs (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [labF_append, h1, h2]

theorem He.coneOk_intro {blk WT RT ST LB : Nat → Nat}
    {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.beq nC nCa = true) (h4 : Nat.ble nCa (nat_lit 1048576) = true)
    (h5 : Nat.blt nf (nat_lit 4294967296) = true)
    (h6 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h7 : Nat.beq S1 (mkS nf nCa) = true)
    (h8 : Nat.beq X0 (nat_lit 1) = true) (h9 : Nat.beq X1 (Nat.succ nf) = true)
    (h10 : HeB.hintsLt WT m (nat_lit 2) Hs = true) (h11 : HeB.labsWF LB nf = true)
    (h12 : Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h13 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h14 : Nat.beq (HeB.runLab WT LB Hs Cs X0) X1 = true) :
    He.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs = true :=
  andB_intro h1 (andB_intro h2 (andB_intro h3 (andB_intro h4 (andB_intro h5 (andB_intro h6
    (andB_intro h7 (andB_intro h8 (andB_intro h9 (andB_intro h10 (andB_intro h11 (andB_intro h12
    (andB_intro h13 h14))))))))))))

theorem Ru.coneOk_intro {blk WT RT ST LB : Nat → Nat}
    {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.beq nC nCa = true) (h4 : Nat.ble nCa (nat_lit 1048576) = true)
    (h5 : Nat.blt nf (nat_lit 4294967296) = true)
    (h6 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h7 : Nat.beq S1 (mkS nf nCa) = true)
    (h8 : Nat.beq X0 (nat_lit 1) = true) (h9 : Nat.beq X1 (Nat.succ nf) = true)
    (h10 : RuB.hintsLt WT m (nat_lit 2) Hs = true) (h11 : HeB.labsWF LB nf = true)
    (h12 : Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h13 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h14 : Nat.beq (RuB.runLab WT LB Hs Cs X0) X1 = true) :
    Ru.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs = true :=
  andB_intro h1 (andB_intro h2 (andB_intro h3 (andB_intro h4 (andB_intro h5 (andB_intro h6
    (andB_intro h7 (andB_intro h8 (andB_intro h9 (andB_intro h10 (andB_intro h11 (andB_intro h12
    (andB_intro h13 h14))))))))))))

theorem LabF.labOk_intro {blk WT RT ST LB : Nat → Nat}
    {INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h1a : Bind.hintsOK WT m nR nS Hs = true)
    (h1b : LCE.relsNorm RT nR = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.beq nC nCa = true) (h4 : Nat.ble nCa (nat_lit 1048576) = true)
    (h5 : Nat.blt nf (nat_lit 4294967296) = true)
    (h6 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h7 : Nat.beq S1 (mkS nf nCa) = true)
    (h8 : Nat.beq X0 (nat_lit 1) = true) (h9 : Nat.beq X1 (Nat.succ nf) = true)
    (h10 : CFSG.KC.LabF.hintsLt WT m K Hs = true) (h11 : HeB.labsWF LB nf = true)
    (h12 : Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h13 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h14 : Nat.beq (CFSG.KC.LabF.runLab WT LB Hs Cs X0) X1 = true) :
    LabF.labOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 Cs = true :=
  andB_intro h1 (andB_intro h1a (andB_intro h1b (andB_intro h2 (andB_intro h3 (andB_intro h4
    (andB_intro h5 (andB_intro h6 (andB_intro h7 (andB_intro h8 (andB_intro h9 (andB_intro h10
    (andB_intro h11 (andB_intro h12 (andB_intro h13 h14))))))))))))))

end CFSG.Certificates.LS

namespace CFSG.Certificates.LS.Asm

meta def lhsArgs (env : Environment) (n : Name) : MetaM (Array Expr) := do
  let some ci := env.find? n | throwError "unknown theorem {n}"
  let some (_, lhs, _) := ci.type.eq? | throwError "not an equation: {n}"
  return lhs.getAppArgs

meta def slices (env : Environment) (F : Name) : MetaM (Array (Name × Array Expr × Expr)) := do
  let mut out := #[]
  let mut k := 0
  while env.contains (F.appendAfter s!"{k}") do
    let n := F.appendAfter s!"{k}"
    let a ← lhsArgs env n
    out := out.push (n, a[0]!.getAppArgs, a[1]!)
    k := k + 1
  if out.isEmpty then throwError "no slice theorems {F}0, …"
  return out

meta partial def joinTree (step : Name) (fixed : Array Expr) (li : Nat)
    (sl : Array (Name × Array Expr × Expr)) (lo hi : Nat) : Expr × Expr × Expr × Expr :=
  if hi = lo + 1 then
    let (n, a, y) := sl[lo]!
    (a[li]!, a[li + 1]!, y, mkConst n)
  else
    let mid := lo + (hi - lo) / 2
    let (l1, x, y, p1) := joinTree step fixed li sl lo mid
    let (l2, _, z, p2) := joinTree step fixed li sl mid hi
    (mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``Nat) l1 l2, x, z,
      mkAppN (mkConst step) (fixed ++ #[l1, l2, x, y, z, p1, p2]))

meta def isTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def lit (n : Nat) : Expr := mkRawNatLit n

end CFSG.Certificates.LS.Asm

open CFSG.Certificates.LS.Asm in
elab "#lab_ok " kind:ident nm:ident p:ident counts:num* : command => do
  let P := p.getId
  let N := nm.getId
  let kd := kind.getId.toString
  liftTermElabM do
    let env ← getEnv
    let sW ← slices env (P ++ `sW)
    let sL ← slices env (P ++ `sL)
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
    let (Cs, S0, S1, pF) := joinTree ``CFSG.Certificates.LS.facts_join (fF.extract 0 5) 5 sW 0 sW.size
    let labStep := if kd == "LabF" then ``CFSG.Certificates.LS.labF_join else .anonymous
    if sL.size > 1 && labStep.isAnonymous then throwError "label slices are joined for LabF only"
    let (CsL, X0, X1, pL) := joinTree labStep (fL.extract 0 3) 3 sL 0 sL.size
    unless CsL == Cs do throwError "the label loop runs over other chunks"
    let c := fun (s : Name) => mkConst (P ++ s)
    withOptions (Elab.async.set · false) do
      let nIds := N ++ `ids
      let type := isTrue (mkApp2 (mkConst ``Nat.beq)
        (mkAppN (mkConst ``CFSG.KC.LceSR.runIds) #[WT, m, Cs, lit 1]) (lit 1))
      CFSG.KC.addThmDecl <| { name := nIds, levelParams := [], type, value := reflBoolTrue }
      let nLabs := N ++ `labs
      let type := isTrue (mkApp2 (mkConst ``CFSG.KC.HeB.labsWF) LB nf)
      CFSG.KC.addThmDecl <| { name := nLabs, levelParams := [], type, value := reflBoolTrue }
      let r := reflBoolTrue
      if kd == "LabF" then
        let #[nR, nS] := counts.map (fun n => lit n.getNat) | throwError "LabF takes nR nS"
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
      else
        let (pred, intro) := if kd == "He" then
            (``CFSG.Certificates.LS.He.coneOk, ``CFSG.Certificates.LS.He.coneOk_intro)
          else (``CFSG.Certificates.LS.Ru.coneOk, ``CFSG.Certificates.LS.Ru.coneOk_intro)
        let args := #[blk, WT, RT, ST, LB, INV, INV8, L, nC, nCa, nf, m, Hs, S0, S1, X0, X1, Cs]
        let pf := mkAppN (mkConst intro) (args ++
          #[c `sH0, c `sH1, c `sH3, r, r, r, r, r, r, c `sH6, mkConst nLabs, mkConst nIds, pF, pL])
        let type := isTrue (mkAppN (mkConst pred) args)
        CFSG.KC.addThmDecl <| { name := N, levelParams := [], type, value := pf }

end
