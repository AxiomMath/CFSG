module

public import Certificates.Data.Kernel.LceSTab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.Certificates.LCE

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

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

theorem facts_step (blk WT : Nat → Nat) (INV nC L : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (runFacts blk WT INV nC L l1 x) y = true)
    (h2 : Nat.beq (runFacts blk WT INV nC L l2 y) z = true) :
    Nat.beq (runFacts blk WT INV nC L (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [runFacts_append, h1, h2]

theorem runCover_append (blk LVs : Nat → Nat) (nf L : Nat) : ∀ (l1 l2 : List Nat) (x : Nat),
    runCover blk LVs nf L (List.append l1 l2) x =
      runCover blk LVs nf L l2 (runCover blk LVs nf L l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (covChunk blk LVs nf L C x) (runCover blk LVs nf L (List.append l1 l2)) =
      runCover blk LVs nf L l2 (strictN (covChunk blk LVs nf L C x) (runCover blk LVs nf L l1))
    rw [strictN_eq, strictN_eq]
    exact runCover_append blk LVs nf L l1 l2 _

theorem cover_step (blk LVs : Nat → Nat) (nf L : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (runCover blk LVs nf L l1 x) y = true)
    (h2 : Nat.beq (runCover blk LVs nf L l2 y) z = true) :
    Nat.beq (runCover blk LVs nf L (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [runCover_append, h1, h2]

theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

theorem andB_right {a b : Bool} (h : andB a b = true) : b = true := by
  cases a
  · exact absurd h (by simp [andB])
  · exact h

theorem chunkLoop_append (g : Nat → Nat → Nat) : ∀ (l1 l2 : List Nat) (x : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (g C S) ih)
        (List.append l1 l2) x =
      List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (g C S) ih) l2
        (List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (g C S) ih)
          l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (g C x) (List.rec (motive := fun _ => Nat → Nat) (fun S => S)
        (fun C _ ih S => strictN (g C S) ih) (List.append l1 l2)) =
      List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (g C S) ih) l2
        (strictN (g C x) (List.rec (motive := fun _ => Nat → Nat) (fun S => S)
          (fun C _ ih S => strictN (g C S) ih) l1))
    rw [strictN_eq, strictN_eq]
    exact chunkLoop_append g l1 l2 _

theorem loop_join (F : List Nat → Nat → Nat)
    (hF : ∀ (l1 l2 : List Nat) (x : Nat), F (List.append l1 l2) x = F l2 (F l1 x))
    (l1 l2 : List Nat) (x y z : Nat) (h1 : Nat.beq (F l1 x) y = true)
    (h2 : Nat.beq (F l2 y) z = true) : Nat.beq (F (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [hF, h1, h2]

theorem loop_join_cast (F : List Nat → Nat → Nat)
    (hF : ∀ (l1 l2 : List Nat) (x : Nat), F (List.append l1 l2) x = F l2 (F l1 x))
    (l1 l2 : List Nat) (x y y' z : Nat) (h1 : Nat.beq (F l1 x) y = true) (hy : y' = y)
    (h2 : Nat.beq (F l2 y') z = true) : Nat.beq (F (List.append l1 l2) x) z = true :=
  loop_join F hF l1 l2 x y z h1 (hy ▸ h2)

theorem lceOk_intro {blk WT RT ST LVs : Nat → Nat}
    {INV INV8 L nC nCl mLV a m Hs nR nS nf : Nat} {Cs CCs : List Nat} {S0 S1 X0 X1 : Nat}
    (h1 : invOK INV INV8 L = true) (h2 : wordsOK WT RT ST INV INV8 m Hs = true)
    (h3 : CFSG.KC.Bind.hintsOK WT m nR nS Hs = true) (h4 : aliveOK LVs mLV nCl a = true)
    (h5 : Nat.beq nC nCl = true) (h6 : Nat.ble nC (nat_lit 1048576) = true)
    (h7 : Nat.blt nf (nat_lit 4294967296) = true)
    (h9 : Nat.blt (nat_lit 0) m = true) (h10 : wtPer WT m = true) (h11 : relsNorm RT nR = true)
    (h12 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true)
    (h13 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h14 : Nat.beq S1 (mkS nf nC) = true) (h15 : Nat.beq X0 (nat_lit 1) = true)
    (h16 : Nat.beq (runCover blk LVs nf L CCs X0) X1 = true)
    (h17 : Nat.beq X1 (Nat.succ nC) = true) :
    lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs S0 S1 X0 X1 = true :=
  andB_intro h1 (andB_intro h2 (andB_intro h3 (andB_intro h4 (andB_intro h5 (andB_intro h6
    (andB_intro h7 (andB_intro h9 (andB_intro h10 (andB_intro h11 (andB_intro h12
    (andB_intro h13 (andB_intro h14 (andB_intro h15 (andB_intro h16 h17))))))))))))))

end CFSG.Certificates.LCE

namespace CFSG.Certificates.LCE.Assemble

meta def sliceArgs (ty : Expr) : MetaM (Name × Array Expr × Expr × Expr × Expr) := do
  let some (_, lhs, _) := ty.eq? | throwError "not an equation: {ty}"
  let args := lhs.getAppArgs
  unless lhs.isAppOfArity ``Nat.beq 2 do throwError "not a Nat.beq: {lhs}"
  let run := args[0]!
  let y := args[1]!
  let rargs := run.getAppArgs
  let some f := run.getAppFn.constName? | throwError "no head constant: {run}"
  let n := rargs.size
  return (f, rargs.extract 0 (n - 2), rargs[n - 2]!, rargs[n - 1]!, y)

meta partial def joinTree (step : Name) (fixed : Array Expr) (slices : Array (Name × Expr × Expr × Expr))
    (lo hi : Nat) : Expr × Expr × Expr × Expr :=
  if hi = lo + 1 then
    let (n, l, x, y) := slices[lo]!
    (l, x, y, mkConst n)
  else
    let mid := lo + (hi - lo) / 2
    let (l1, x, y, p1) := joinTree step fixed slices lo mid
    let (l2, _, z, p2) := joinTree step fixed slices mid hi
    (mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``Nat) l1 l2, x, z,
      mkAppN (mkConst step) (fixed ++ #[l1, l2, x, y, z, p1, p2]))

meta partial def loopTree (Fe hF : Expr) (slices : Array (Name × Expr × Expr × Expr))
    (lo hi : Nat) : Expr × Expr × Expr × Expr :=
  if hi ≤ lo + 1 then
    let (n, l, x, y) := slices[lo]!
    (l, x, y, mkConst n)
  else
    let mid := lo + (hi - lo) / 2
    let (l1, x, y, p1) := loopTree Fe hF slices lo mid
    let (l2, y', z, p2) := loopTree Fe hF slices mid hi
    let pf := if y' == y then
        mkAppN (mkConst ``CFSG.Certificates.LCE.loop_join) #[Fe, hF, l1, l2, x, y, z, p1, p2]
      else
        mkAppN (mkConst ``CFSG.Certificates.LCE.loop_join_cast)
          #[Fe, hF, l1, l2, x, y, y', z, p1, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) y', p2]
    (mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``Nat) l1 l2, x, z, pf)

end CFSG.Certificates.LCE.Assemble

open CFSG.Certificates.LCE.Assemble in
elab "#lces_join " nm:ident f:ident lo:num hi:num : command => do
  let F := f.getId
  let thms := (List.range (hi.getNat - lo.getNat)).map fun k => F.appendAfter s!"{lo.getNat + k}"
  liftTermElabM do
    let env ← getEnv
    let mut slices : Array (Name × Expr × Expr × Expr) := #[]
    let mut head : Name := .anonymous
    let mut fixed : Array Expr := #[]
    for t in thms do
      let some ci := env.find? t | throwError "unknown theorem {t}"
      let (fn, fx, l, x, y) ← sliceArgs ci.type
      if head.isAnonymous then
        head := fn
        fixed := fx
      unless fn == head && fx == fixed do throwError "{t}: slice of another loop"
      slices := slices.push (t, l, x, y)
    let step := if head == ``CFSG.KC.LceS.runFacts then ``CFSG.Certificates.LCE.facts_step
      else if head == ``CFSG.KC.LceS.runCover then ``CFSG.Certificates.LCE.cover_step
      else .anonymous
    if step.isAnonymous then throwError "unknown loop {head}"
    let (l, x, z, pf) := joinTree step fixed slices 0 slices.size
    let lhs := mkApp2 (mkConst ``Nat.beq) (mkAppN (mkConst head) (fixed ++ #[l, x])) z
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name := nm.getId, levelParams := [], type, value := pf }

open CFSG.Certificates.LCE.Assemble in
elab "#loop_join " nm:ident app:ident f:ident lo:num hi:num : command => do
  let F := f.getId
  let thms := (List.range (hi.getNat - lo.getNat)).map fun k => F.appendAfter s!"{lo.getNat + k}"
  liftTermElabM do
    let env ← getEnv
    let mut slices : Array (Name × Expr × Expr × Expr) := #[]
    let mut head : Name := .anonymous
    let mut fixed : Array Expr := #[]
    for t in thms do
      let some ci := env.find? t | throwError "unknown theorem {t}"
      let (fn, fx, l, x, y) ← sliceArgs ci.type
      if head.isAnonymous then
        head := fn
        fixed := fx
      unless fn == head && fx == fixed do throwError "{t}: slice of another loop"
      slices := slices.push (t, l, x, y)
    let Fe := mkAppN (mkConst head) fixed
    let hF := mkAppN (mkConst app.getId) fixed
    let (l, x, z, pf) := loopTree Fe hF slices 0 slices.size
    let lhs := mkApp2 (mkConst ``Nat.beq) (mkAppN Fe #[l, x]) z
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name := nm.getId, levelParams := [], type, value := pf }

open CFSG.Certificates.LCE.Assemble in
elab "#lces_ok " nm:ident hI:ident hW:ident hH:ident hA:ident hC:ident hP:ident
    hN:ident hF:ident hV:ident : command => do
  liftTermElabM do
    let env ← getEnv
    let ty := fun (i : Ident) => do
      let some ci := env.find? i.getId | throwError "unknown theorem {i.getId}"
      let some (_, lhs, _) := ci.type.eq? | throwError "not an equation: {i.getId}"
      pure lhs.getAppArgs
    let aI ← ty hI
    let aW ← ty hW
    let aH ← ty hH
    let aA ← ty hA
    let aC ← ty hC
    let aN ← ty hN
    let (_, fF, Cs, S0, S1) ← sliceArgs (← getConstInfo hF.getId).type
    let (_, fV, CCs, X0, X1) ← sliceArgs (← getConstInfo hV.getId).type
    let blk := fF[0]!
    let WT := fF[1]!
    let INV := fF[2]!
    let nC := fF[3]!
    let L := fF[4]!
    let LVs := fV[1]!
    let nf := fV[2]!
    let INV8 := aI[1]!
    let RT := aW[1]!
    let ST := aW[2]!
    let m := aW[5]!
    let Hs := aW[6]!
    let nR := aH[2]!
    let nS := aH[3]!
    let mLV := aA[1]!
    let nCl := aA[2]!
    let a := aA[3]!
    let _ := aC
    let _ := aN
    let args := #[blk, WT, RT, ST, LVs, INV, INV8, L, nC, nCl, mLV, a, m, Hs, nR, nS, nf, Cs, CCs,
      S0, S1, X0, X1]
    let c := fun (i : Ident) => mkConst i.getId
    let pf := mkAppN (mkConst ``CFSG.Certificates.LCE.lceOk_intro) (args ++
      #[c hI, c hW, c hH, c hA, c hC, reflBoolTrue, reflBoolTrue, reflBoolTrue, c hP, c hN,
        reflBoolTrue, c hF, reflBoolTrue, reflBoolTrue, c hV, reflBoolTrue])
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.Certificates.LCE.lceOk) args) (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name := nm.getId, levelParams := [], type, value := pf }

end
