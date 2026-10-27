module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Lib
public import CFSG.Certificates.Kernel.Common.Bind
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception
public import Std.Tactic.BVDecide.Normalize.Prop

open Lean Elab Command

public section

namespace CFSG.Certificates.LS

open CFSG.KC CFSG.KC.LceS

@[expose] noncomputable def went (RT ST : Nat → Nat) (INV INV8 w r : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) true
      (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r)))
      (Nat.beq (wKind w) (nat_lit 3)))
    (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
    (Nat.beq (wKind w) (nat_lit 2))

theorem andB_eq_true (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem wordsOK_aux (WT RT ST : Nat → Nat) (INV INV8 m : Nat) : ∀ k, k ≤ m → ∀ H,
    (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun k ih H => andB
        ((fun w r => went RT ST INV INV8 w r) (WT (Nat.sub m (Nat.succ k))) (Nat.land H 65535))
        (ih (Nat.shiftRight H 16))) k H = true) ↔
      ∀ i < k, went RT ST INV INV8 (WT (m - k + i)) (H / 2 ^ (16 * i) % 65536) = true
  | 0, _, _ => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | k + 1, hk, H => by
    refine Iff.trans (andB_eq_true _ _) ?_
    have hl : Nat.land H 65535 = H / 2 ^ (16 * 0) % 65536 := by
      rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      exact Nat.and_two_pow_sub_one_eq_mod H 16
    have hr : Nat.shiftRight H 16 = H / 2 ^ 16 := Nat.shiftRight_eq_div_pow H 16
    rw [wordsOK_aux WT RT ST INV INV8 m k (by omega) (Nat.shiftRight H 16), hr]
    have es : ∀ i, m - (k + 1) + (i + 1) = m - k + i := fun i => by omega
    have ed : ∀ i, H / 2 ^ (16 * (i + 1)) = H / 2 ^ 16 / 2 ^ (16 * i) := fun i => by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ, Nat.add_comm (16 * i)]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      rcases i with _ | i
      · rw [← hl]
        exact h0
      · rw [es, ed]
        exact hs i (by omega)
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have := h 0 (by omega)
        rw [← hl] at this
        exact this
      · have := h (i + 1) (by omega)
        rw [es, ed] at this
        exact this

theorem wordsOK_iff (WT RT ST : Nat → Nat) (INV INV8 m Hs : Nat) :
    wordsOK WT RT ST INV INV8 m Hs = true ↔
      ∀ i < m, went RT ST INV INV8 (WT i) (Hs / 2 ^ (16 * i) % 65536) = true := by
  have h := wordsOK_aux WT RT ST INV INV8 m m (Nat.le_refl m) Hs
  simp only [Nat.sub_self, Nat.zero_add] at h
  exact h

theorem wordsOK_join (WT RT ST : Nat → Nat) (INV INV8 o a b H1 H2 : Nat)
    (h1 : wordsOK (CFSG.KC.RuBA.shiftF WT o) RT ST INV INV8 a H1 = true)
    (h2 : wordsOK (CFSG.KC.RuBA.shiftF WT (Nat.add o a)) RT ST INV INV8 b H2 = true)
    (hH : Nat.blt H1 (Nat.shiftLeft 1 (Nat.mul 16 a)) = true) :
    wordsOK (CFSG.KC.RuBA.shiftF WT o) RT ST INV INV8 (Nat.add a b)
      (Nat.add H1 (Nat.mul (Nat.shiftLeft 1 (Nat.mul 16 a)) H2)) = true := by
  have e2 : Nat.shiftLeft 1 (Nat.mul 16 a) = 2 ^ (16 * a) :=
    (Nat.shiftLeft_eq 1 (16 * a)).trans (Nat.one_mul _)
  rw [e2] at hH ⊢
  rw [wordsOK_iff] at h1 h2 ⊢
  have hlt : H1 < 2 ^ (16 * a) := by
    rw [Nat.blt_eq] at hH
    exact hH
  simp only [Nat.add_eq, Nat.mul_eq] at h2 ⊢
  intro i hi
  have hw : CFSG.KC.RuBA.shiftF WT o i = WT (i + o) := rfl
  rw [hw]
  rcases Nat.lt_or_ge i a with hia | hia
  · have e : (H1 + 2 ^ (16 * a) * H2) / 2 ^ (16 * i) % 65536 = H1 / 2 ^ (16 * i) % 65536 := by
      have hp : 2 ^ (16 * a) = 2 ^ (16 * i) * (65536 * 2 ^ (16 * (a - i - 1))) := by
        have h6 : (65536 : Nat) = 2 ^ 16 := rfl
        rw [h6, ← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      rw [hp, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_assoc,
        Nat.add_mul_mod_self_left]
    rw [e]
    exact h1 i hia
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hia
    have e : (H1 + 2 ^ (16 * a) * H2) / 2 ^ (16 * (a + j)) % 65536 = H2 / 2 ^ (16 * j) % 65536 := by
      rw [Nat.mul_add, Nat.pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
    rw [e]
    have := h2 j (by omega)
    have hw2 : CFSG.KC.RuBA.shiftF WT (o + a) j = WT (j + (o + a)) := rfl
    have hj : a + j + o = j + (o + a) := by omega
    rw [hw2] at this
    rw [hj]
    exact this

theorem wordsOK_shift0 (WT RT ST : Nat → Nat) (INV INV8 m Hs : Nat)
    (h : wordsOK (CFSG.KC.RuBA.shiftF WT 0) RT ST INV INV8 m Hs = true) :
    wordsOK WT RT ST INV INV8 m Hs = true := h

end CFSG.Certificates.LS

namespace CFSG.Certificates.LS.Asm

meta def lhsArgs' (env : Environment) (n : Name) : MetaM (Array Expr) := do
  let some ci := env.find? n | throwError "unknown theorem {n}"
  let some (_, lhs, _) := ci.type.eq? | throwError "not an equation: {n}"
  return lhs.getAppArgs

end CFSG.Certificates.LS.Asm

open CFSG.Certificates.LS.Asm in
elab "#words_join " nm:ident p:ident n:num nr:num ns:num : command => do
  let P := p.getId
  let cnt := n.getNat
  liftTermElabM do
    let env ← getEnv
    let mut sl : Array (Name × Array Expr) := #[]
    for k in [0:cnt] do
      let t := P ++ Name.mkSimple s!"sH0_{k}"
      sl := sl.push (t, ← lhsArgs' env t)
    let a0 := sl[0]!.2
    let WT := a0[0]!.getAppArgs[0]!
    let rest := a0.extract 1 5
    let a := a0[5]!
    for (t, x) in sl do
      unless x.extract 1 5 == rest && x[5]! == a && x[0]!.getAppArgs[0]! == WT do
        throwError "{t}: a slice of another table"
    let nat := fun (v : Nat) => mkRawNatLit v
    let some aV := a.rawNatLit? | throwError "slice size is not a literal"
    let bound := mkApp2 (mkConst ``Nat.shiftLeft) (nat 1) (mkApp2 (mkConst ``Nat.mul) (nat 16) a)
    let (tl, xl) := sl[cnt - 1]!
    let mut m := a
    let mut H := xl[6]!
    let mut pf := mkConst tl
    for k' in [0:cnt - 1] do
      let k := cnt - 2 - k'
      let (t, x) := sl[k]!
      let o := x[0]!.getAppArgs[1]!
      let H1 := x[6]!
      let hH := reflBoolTrue
      pf := mkAppN (mkConst ``CFSG.Certificates.LS.wordsOK_join)
        (#[WT] ++ rest ++ #[o, a, m, H1, H, mkConst t, pf, hH])
      H := mkApp2 (mkConst ``Nat.add) H1 (mkApp2 (mkConst ``Nat.mul) bound H)
      m := mkApp2 (mkConst ``Nat.add) a m
    let total := nat (aV * cnt)
    pf := mkAppN (mkConst ``CFSG.Certificates.LS.wordsOK_shift0) (#[WT] ++ rest ++ #[total, H, pf])
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KC.LceS.wordsOK) (#[WT] ++ rest ++ #[total, H])) (mkConst ``Bool.true)
    let nR := nat nr.getNat
    let nS := nat ns.getNat
    let htype := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KC.Bind.hintsOK) #[WT, total, nR, nS, H]) (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) do
      CFSG.KC.addThmDecl <| { name := nm.getId, levelParams := [], type, value := pf }
      let hn := nm.getId ++ `hints
      CFSG.KC.addThmDecl <| { name := hn, levelParams := [], type := htype, value := reflBoolTrue }

end
