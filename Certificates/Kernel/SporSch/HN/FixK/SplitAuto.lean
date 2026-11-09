module

public import Certificates.Kernel.SporSch.HN.FixK.Split
public import Certificates.Kernel.SporSch.HN.FixK.Tab13608
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

open Lean Elab Command

public section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX CFSG.KD.HN13608

@[expose] noncomputable def dotPart (lo n v : Nat) : Bool :=
  Nat.beq (dotSum TX CM3 M MR L1 ONES GQ (nat_lit 1) lo n) v

private theorem dt_strictN (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem dotSum_succ (T : Nat → Nat) (CM3 M MR L1 ONES G v lo n : Nat) :
    dotSum T CM3 M MR L1 ONES G v lo (n + 1) =
      dotSum T CM3 M MR L1 ONES G v lo n +
        dotLeaf T CM3 M MR L1 ONES G v (lo + n) (CFSG.KS.SporSch.hnxC (lo + n)) := by
  show CFSG.KC.Loop.strictN (dotSum T CM3 M MR L1 ONES G v lo n) (fun a => Nat.add a
      (dotLeaf T CM3 M MR L1 ONES G v (Nat.add lo n) (CFSG.KS.SporSch.hnxC (Nat.add lo n)))) = _
  rw [dt_strictN]
  rfl

theorem dotSum_append (T : Nat → Nat) (CM3 M MR L1 ONES G v lo a : Nat) : ∀ b,
    dotSum T CM3 M MR L1 ONES G v lo (a + b) =
      dotSum T CM3 M MR L1 ONES G v lo a + dotSum T CM3 M MR L1 ONES G v (lo + a) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, dotSum_succ, dotSum_append T CM3 M MR L1 ONES G v lo a b, dotSum_succ]
    simp only [Nat.add_assoc]

theorem dotPart_add {lo a b va vb : Nat} (ha : dotPart lo a va = true)
    (hb : dotPart (lo + a) b vb = true) : dotPart lo (a + b) (va + vb) = true := by
  have h1 : dotSum TX CM3 M MR L1 ONES GQ (nat_lit 1) lo a = va := Nat.eq_of_beq_eq_true ha
  have h2 : dotSum TX CM3 M MR L1 ONES GQ (nat_lit 1) (lo + a) b = vb := Nat.eq_of_beq_eq_true hb
  show Nat.beq (dotSum TX CM3 M MR L1 ONES GQ (nat_lit 1) lo (a + b)) (va + vb) = true
  rw [dotSum_append, h1, h2]
  exact Nat.beq_refl _

theorem dot13608_of8 (k n0 n1 n2 n3 n4 n5 n6 n7 v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (h0 : dotPart (2227 * k) n0 v0 = true)
    (h1 : dotPart (2227 * k + n0) n1 v1 = true)
    (h2 : dotPart (2227 * k + (n0 + n1)) n2 v2 = true)
    (h3 : dotPart (2227 * k + (n0 + n1 + n2)) n3 v3 = true)
    (h4 : dotPart (2227 * k + (n0 + n1 + n2 + n3)) n4 v4 = true)
    (h5 : dotPart (2227 * k + (n0 + n1 + n2 + n3 + n4)) n5 v5 = true)
    (h6 : dotPart (2227 * k + (n0 + n1 + n2 + n3 + n4 + n5)) n6 v6 = true)
    (h7 : dotPart (2227 * k + (n0 + n1 + n2 + n3 + n4 + n5 + n6)) n7 v7 = true)
    (hn : n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 = fixLen k)
    (hv : v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 = DOT13608 k) :
    dot13608 k = true := by
  have h := dotPart_add (dotPart_add (dotPart_add (dotPart_add (dotPart_add (dotPart_add
    (dotPart_add h0 h1) h2) h3) h4) h5) h6) h7
  rw [hn, hv] at h
  exact h

end CFSG.KD.HNXK

namespace CFSG.KD.HNXK.FixAuto

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.HNXK.FixGen

meta def partVal (part : Name) (pre : Array Expr) (lo n : Nat) : CoreM Nat := do
  let ci ← getConstInfo part
  let some body := ci.value? | throwError "partVal: {part} has no value"
  let e := (body.beta (pre ++ #[lit lo, lit n, lit 0])).headBeta
  match e.getAppFnArgs with
  | (``Nat.beq, #[x, _]) => CFSG.KC.Benes.kNat s!"{part} {lo} {n}" x
  | _ => throwError "partVal: {part} is not a Nat.beq"

meta def emitAuto (P : Name) (fE : Expr) (part : Name) (pre : Array Expr) (k0 c : Nat)
    (mkC : Nat → Array Expr → Array Expr → Array Expr → Nat → Nat → Expr) : CoreM Unit := do
  for i in [0:c] do
    let k := k0 + i
    let len := if k < 7 then 2227 else 2224
    let b := fun j => len * j / 8
    let mut qs : Array Expr := #[]
    let mut vals : Array Nat := #[]
    for j in [0:8] do
      let lo := 2227 * k + b j
      let n := b (j + 1) - b j
      let v ← partVal part pre lo n
      vals := vals.push v
      let nm := P ++ Name.mkSimple s!"q{i}_{j}"
      let ty := isTrueB (mkAppN (mkConst part) (pre ++ #[lit lo, lit n, lit v]))
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
      qs := qs.push (mkConst nm)
    let ns := (List.range 8).toArray.map fun j => lit (b (j + 1) - b j)
    let vv := vals.map lit
    let tot := vals.foldl (· + ·) 0
    let cn := P ++ Name.mkSimple s!"c{i}"
    let cty := isTrueB (mkApp fE (lit i))
    let pf := mkC k ns vv qs len tot
    CFSG.KC.addThmDecl <| { name := cn, levelParams := [], type := cty, value := pf }
  let pE := mkLambda `i .default natT (isTrueB (mkApp fE (mkBVar 0)))
  let v := forallChain pE c fun i => mkConst (P ++ Name.mkSimple s!"c{i}")
  let ty := mkForall `i .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit c])
    (isTrueB (mkApp fE (mkBVar 1))))
  CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := v }

end CFSG.KD.HNXK.FixAuto

open CFSG.KC.Tab CFSG.KD.HNXK.FixGen CFSG.KD.HNXK.FixAuto in
elab "#kss_fix_auto " pre:ident fId:ident gId:ident vId:ident mm:num k0:num cc:num : command => do
  let P := pre.getId
  let m := mm.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let vN ← liftCoreM <| realizeGlobalConstNoOverload vId
  let gE := mkConst gN
  liftCoreM <| withOptions (Elab.async.set · false) do
    emitAuto P (mkConst fN) ``CFSG.KD.HNXK.fixPart #[gE] k0.getNat cc.getNat
      fun k ns vv qs len tot => mkAppN (mkConst ``CFSG.KD.HNXK.fixOk_of8)
        (#[gE, mkConst vN, lit m, lit k] ++ ns ++ vv ++ qs ++ #[reflN len, reflN tot])

open CFSG.KC.Tab CFSG.KD.HNXK.FixGen CFSG.KD.HNXK.FixAuto in
elab "#kss_dot_auto " pre:ident fId:ident k0:num cc:num : command => do
  let P := pre.getId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  liftCoreM <| withOptions (Elab.async.set · false) do
    emitAuto P (mkConst fN) ``CFSG.KD.HNXK.dotPart #[] k0.getNat cc.getNat
      fun k ns vv qs len tot => mkAppN (mkConst ``CFSG.KD.HNXK.dot13608_of8)
        (#[lit k] ++ ns ++ vv ++ qs ++ #[reflN len, reflN tot])

end
