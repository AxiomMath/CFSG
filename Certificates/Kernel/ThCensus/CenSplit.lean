module

public import Certificates.Kernel.ThCensus.WordChecks
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

open Lean Elab Command

public section

namespace CFSG.KC.ThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Loop

@[expose] noncomputable def wordPart (RB : Nat → Nat) (c rm r0 r1 r2 r3 n J S S' : Nat) : Bool :=
  Nat.beq (wordR RB c rm r0 r1 r2 r3 n J S) S'

private theorem cs_strictN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem wordR_succ (RB : Nat → Nat) (c rm r0 r1 r2 r3 n J S : Nat) :
    wordR RB c rm r0 r1 r2 r3 (n + 1) J S =
      wordR RB c rm r0 r1 r2 r3 n (Nat.shiftRight J 2)
        (mulB c rm S (RB (letR r0 r1 r2 r3 (Nat.land J 3)))) := by
  show strictN _ _ = _
  rw [cs_strictN]
  rfl

theorem wordR_add (RB : Nat → Nat) (c rm r0 r1 r2 r3 b : Nat) : ∀ (a J S : Nat),
    wordR RB c rm r0 r1 r2 r3 (Nat.add a b) J S =
      wordR RB c rm r0 r1 r2 r3 b (Nat.shiftRight J (Nat.mul (nat_lit 2) a))
        (wordR RB c rm r0 r1 r2 r3 a J S)
  | 0, J, S => by
    show wordR RB c rm r0 r1 r2 r3 (0 + b) J S = wordR RB c rm r0 r1 r2 r3 b (J >>> (2 * 0)) S
    rw [Nat.zero_add, Nat.mul_zero, Nat.shiftRight_zero]
  | a + 1, J, S => by
    have e : Nat.add (a + 1) b = (Nat.add a b) + 1 := by simp only [Nat.add_eq]; omega
    rw [e, wordR_succ, wordR_add RB c rm r0 r1 r2 r3 b a, wordR_succ]
    congr 1
    show (J >>> 2) >>> (2 * a) = J >>> (2 * (a + 1))
    rw [← Nat.shiftRight_add]
    congr 1
    omega

theorem wordR_last (RB : Nat → Nat) (c rm r0 r1 r2 r3 a J S Sf : Nat)
    (p : wordPart RB c rm r0 r1 r2 r3 a J S Sf = true) :
    wordR RB c rm r0 r1 r2 r3 a J S = Sf :=
  Nat.eq_of_beq_eq_true p

theorem wordR_chain (RB : Nat → Nat) (c rm r0 r1 r2 r3 a b J S S1 Sf : Nat)
    (p : wordPart RB c rm r0 r1 r2 r3 a J S S1 = true)
    (h : wordR RB c rm r0 r1 r2 r3 b (Nat.shiftRight J (Nat.mul (nat_lit 2) a)) S1 = Sf) :
    wordR RB c rm r0 r1 r2 r3 (Nat.add a b) J S = Sf := by
  rw [wordR_add, Nat.eq_of_beq_eq_true p, h]

theorem wordR_eq_of (RB : Nat → Nat) (c rm r0 r1 r2 r3 n n' w J S Sf : Nat)
    (hn : n = n') (hw : w = J) (h : wordR RB c rm r0 r1 r2 r3 n' J S = Sf) :
    wordR RB c rm r0 r1 r2 r3 n w S = Sf := by
  subst hn hw
  exact h

theorem cenOK_of (RB PW : Nat → Nat) (c rm ONE r2 rz rs ru : Nat) (T e : List Nat) (w Sf : Nat)
    (hW : wordR RB c rm (nat_lit 1) (nat_lit 2) r2 (nat_lit 0) (e.getD 1 0) w ONE = Sf)
    (h : andB (Nat.blt (e.getD 0 0) (nat_lit 6))
      (conjEq c rm (nfM PW c rm ONE T) (clsM RB c rm rz rs ru (e.getD 0 0)) Sf) = true) :
    cenOK RB PW c rm ONE r2 rz rs ru T e w = true := by
  unfold cenOK
  rw [hW]
  exact h

end CFSG.KC.ThCensus

namespace CFSG.KC.ThCensus.Split

meta def litN (n : Nat) : Expr := mkRawNatLit n

meta def natE : Expr := mkConst ``Nat

meta def isTrueE (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def reflNat (e : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) natE e

meta def addE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.add) a b

meta def nextJ (J a : Expr) : Expr :=
  mkApp2 (mkConst ``Nat.shiftRight) J (mkApp2 (mkConst ``Nat.mul) (litN 2) a)

meta def instForall (t : Expr) (args : Array Expr) : Expr := Id.run do
  let mut t := t
  for a in args do
    t := t.bindingBody!.instantiate1 a
  return t

meta def emitOne (F : Name) (j L : Nat) : CoreM Unit := do
  let ci ← getConstInfo F
  let some body := ci.value? | throwError "{F} has no value"
  let app := (body.beta #[litN j]).headBeta
  let args := app.getAppArgs
  unless app.isAppOfArity ``CFSG.KC.ThCensus.cenOK 12 do
    throwError "{F} {j}: not a cenOK application"
  let RB := args[0]!
  let c := args[2]!
  let rm := args[3]!
  let ONE := args[4]!
  let r2 := args[5]!
  let w := args[11]!
  let ofTy := (← getConstInfo ``CFSG.KC.ThCensus.cenOK_of).type
  let hWTy := (instForall ofTy (args.push (mkConst ``Nat.zero))).bindingDomain!
  let wr := hWTy.getAppArgs[1]!
  let nE := wr.getAppArgs[7]!
  let n ← CFSG.KC.Benes.kNat s!"{F}{j} length" nE
  let Jw ← CFSG.KC.Benes.kNat s!"{F}{j} word" w
  let k := max 1 ((n + L - 1) / L)
  let lens := (List.range k).toArray.map fun i => n * (i + 1) / k - n * i / k
  let pre := #[RB, c, rm, litN 1, litN 2, r2, litN 0]
  let mut Js : Array Expr := #[litN Jw]
  let mut Ss : Array Expr := #[ONE]
  let mut vals : Array Nat := #[]
  for i in [0:k] do
    let a := litN lens[i]!
    let v ← CFSG.KC.Benes.kNat s!"{F}{j} piece {i}"
      (mkAppN (mkConst ``CFSG.KC.ThCensus.wordR) (pre ++ #[a, Js[i]!, Ss[i]!]))
    vals := vals.push v
    Js := Js.push (nextJ Js[i]! a)
    Ss := Ss.push (litN v)
  let Sf := litN vals[k - 1]!
  let pname := fun (i : Nat) => F.appendAfter s!"w{j}_{i}"
  for i in [0:k] do
    let ty := isTrueE (mkAppN (mkConst ``CFSG.KC.ThCensus.wordPart)
      (pre ++ #[litN lens[i]!, Js[i]!, Ss[i]!, Ss[i + 1]!]))
    CFSG.KC.addThmDecl { name := pname i, levelParams := [], type := ty, value := reflTrue }
  let mut rest : Array Expr := Array.replicate (k + 1) (litN 0)
  rest := rest.set! (k - 1) (litN lens[k - 1]!)
  for t in [0:k - 1] do
    let i := k - 2 - t
    rest := rest.set! i (addE (litN lens[i]!) rest[i + 1]!)
  let mut h := mkAppN (mkConst ``CFSG.KC.ThCensus.wordR_last)
    (pre ++ #[litN lens[k - 1]!, Js[k - 1]!, Ss[k - 1]!, Sf, mkConst (pname (k - 1))])
  for t in [0:k - 1] do
    let i := k - 2 - t
    h := mkAppN (mkConst ``CFSG.KC.ThCensus.wordR_chain)
      (pre ++ #[litN lens[i]!, rest[i + 1]!, Js[i]!, Ss[i]!, Ss[i + 1]!, Sf, mkConst (pname i), h])
  let hW := mkAppN (mkConst ``CFSG.KC.ThCensus.wordR_eq_of)
    (pre ++ #[nE, rest[0]!, w, litN Jw, ONE, Sf, reflNat rest[0]!, reflNat (litN Jw), h])
  let pf := mkAppN (mkConst ``CFSG.KC.ThCensus.cenOK_of) (args ++ #[Sf, hW, reflTrue])
  let ty := isTrueE (mkApp (mkConst F) (litN j))
  CFSG.KC.addThmDecl { name := F.appendAfter s!"{j}", levelParams := [], type := ty, value := pf }

end CFSG.KC.ThCensus.Split

elab "#thc_cen_split " f:ident lo:num hi:num ll:num : command => do
  let F ← liftCoreM <| realizeGlobalConstNoOverload f
  liftCoreM <| withOptions (Elab.async.set · false) do
    for j in [lo.getNat:hi.getNat] do
      CFSG.KC.ThCensus.Split.emitOne F j ll.getNat

end
