module

public import CFSG.Certificates.Kernel.He.Bound.LabRange
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KC.HeB

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def labRangeK (LB : Nat → Nat) (lo k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => andB (labWF (LB (Nat.add lo j))) ih) k

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem labRangeK_sound {LB : Nat → Nat} {lo : Nat} : ∀ {k : Nat}, labRangeK LB lo k = true →
    ∀ j < k, labWF (LB (lo + j)) = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, h, j, hj => by
    have h' : andB (labWF (LB (Nat.add lo k))) (labRangeK LB lo k) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact labRangeK_sound h2 j hjk
    · have : j = k := by omega
      subst this
      exact h1

theorem allBelow_of {m : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) (hi : Nat) :
    allBelow m hi f = true := by
  have hg : ∀ i : Nat, (Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m)) = true := by
    intro i
    cases hb : Nat.blt i m
    · rfl
    · exact h i (Nat.le_of_ble_eq_true hb)
  have inner : ∀ c k : Nat, Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        (Bool.rec (motive := fun _ => Bool) true (f (Nat.add c l)) (Nat.blt (Nat.add c l) m))) k
      = true := by
    intro c k
    induction k with
    | zero => rfl
    | succ k ih =>
      change Bool.rec (motive := fun _ => Bool) false _
        (Bool.rec (motive := fun _ => Bool) true (f (Nat.add c k)) (Nat.blt (Nat.add c k) m)) = true
      rw [hg]
      exact ih
  induction hi with
  | zero => rfl
  | succ hi ih =>
    change Bool.rec (motive := fun _ => Bool) false _ _ = true
    rw [inner]
    exact ih

theorem labsWF_of_ranges {LB : Nat → Nat} {nf CH S : Nat} (hS : nf ≤ S * CH)
    (h : ∀ s < S, labRangeK LB (s * CH) CH = true) : labsWF LB nf = true := by
  apply allBelow_of
  intro i hi
  have hCH : 0 < CH := by
    rcases Nat.eq_zero_or_pos CH with h0 | h0
    · subst h0; omega
    · exact h0
  have hs : i / CH < S := by
    rw [Nat.div_lt_iff_lt_mul hCH]
    omega
  have := labRangeK_sound (h (i / CH) hs) (i % CH) (Nat.mod_lt i hCH)
  rwa [Nat.div_add_mod'] at this

theorem forall_lt_succ {P : Nat → Prop} {S : Nat} (h : ∀ s < S, P s) (hS : P S) :
    ∀ s < S + 1, P s := by
  intro s hs
  rcases Nat.lt_or_ge s S with h1 | h1
  · exact h s h1
  · have : s = S := by omega
    subst this
    exact hS

theorem forall_lt_zero {P : Nat → Prop} : ∀ s < 0, P s := fun s hs => absurd hs (Nat.not_lt_zero s)

end CFSG.KC.HeB

elab "#labs_ok " nm:ident lb:ident nf:num ch:num : command => do
  let N := nm.getId
  let nf := nf.getNat
  let CH := ch.getNat
  let S := (nf + CH - 1) / CH
  liftTermElabM do
    let LB ← realizeGlobalConstNoOverload lb
    let lbE := mkConst LB
    let lit := mkRawNatLit
    let isTrue := fun (b : Expr) => mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) do
      for s in [0:S] do
        let ty := isTrue (mkAppN (mkConst ``CFSG.KC.HeB.labRangeK) #[lbE, lit (s * CH), lit CH])
        let nm := N.appendAfter s!"_s{s}"
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
      let natE := mkConst ``Nat
      let mul := fun (a b : Expr) => mkAppN (mkConst ``HMul.hMul [0, 0, 0])
        #[natE, natE, natE, mkApp2 (mkConst ``instHMul [0]) natE (mkConst ``instMulNat), a, b]
      let P := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KC.HeB.labRangeK)
        #[lbE, mul (mkBVar 0) (lit CH), lit CH]))
      let mut pf := mkApp (mkConst ``CFSG.KC.HeB.forall_lt_zero) P
      for s in [0:S] do
        pf := mkAppN (mkConst ``CFSG.KC.HeB.forall_lt_succ) #[P, lit s, pf,
          mkConst (N.appendAfter s!"_s{s}")]
      let ty := isTrue (mkApp2 (mkConst ``CFSG.KC.HeB.labsWF) lbE (lit nf))
      let hS := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit nf) (mul (lit S) (lit CH))
        reflBoolTrue
      let val := mkAppN (mkConst ``CFSG.KC.HeB.labsWF_of_ranges) #[lbE, lit nf, lit CH, lit S, hS, pf]
      CFSG.KC.addThmDecl <| { name := N, levelParams := [], type := ty, value := val }

end
