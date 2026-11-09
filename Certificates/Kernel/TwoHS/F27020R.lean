module

public import Certificates.Kernel.TwoHS.F27020
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.TwoHS
  CFSG.Sporadic.Recognition.HSMultiplier

theorem strictB_eqR (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bind2_eqR (f : Fin 2 → Nat) (k : (Fin 2 → Nat) → Bool) : bind2 f k = k f := by
  unfold bind2
  simp only [strictB_eqR]
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem bind6_eqR (f : Fin 6 → Nat) (k : (Fin 6 → Nat) → Bool) : bind6 f k = k f := by
  unfold bind6
  simp only [strictB_eqR]
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

theorem bindGlue (F2 G2 : Fin 2 → Nat) (E : (Fin 2 → Nat) → (Fin 2 → Nat) → Fin 6 → Nat)
    (B : (Fin 6 → Nat) → Bool) (X : Fin 6 → Nat) (hX : ∀ j, E F2 G2 j = X j) (hB : B X = true) :
    (bind2 F2 fun A => bind2 G2 fun AI => bind6 (fun j => E A AI j) B) = true := by
  simp only [bind2_eqR, bind6_eqR]
  have hf : (fun j => E F2 G2 j) = X := funext hX
  rw [hf]
  exact hB

theorem finRange4_allR (P : Fin 4 → Bool) (h0 : P ⟨0, by decide⟩ = true) (h1 : P ⟨1, by decide⟩ = true)
    (h2 : P ⟨2, by decide⟩ = true) (h3 : P ⟨3, by decide⟩ = true) : (List.finRange 4).all P = true := by
  rw [List.all_eq_true]
  intro i _
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3

#kc_natval XR0 := EV3 A3 A3I (hsGenWords.getD 0 [])
#kc_natval XR1 := EV3 A3 A3I (hsGenWords.getD 1 [])
#kc_natval XR2 := EV3 A3 A3I (hsGenWords.getD 2 [])
#kc_natval XR3 := EV3 A3 A3I (hsGenWords.getD 3 [])
#kc_natval XR4 := EV3 A3 A3I (hsGenWords.getD 4 [])
#kc_natval XR5 := EV3 A3 A3I (hsGenWords.getD 5 [])

theorem xr0 : EV3 A3 A3I (hsGenWords.getD (⟨0, by decide⟩ : Fin 6).val []) =
    sel6 XR0 XR1 XR2 XR3 XR4 XR5 ⟨0, by decide⟩ := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xr1 : EV3 A3 A3I (hsGenWords.getD (⟨1, by decide⟩ : Fin 6).val []) =
    sel6 XR0 XR1 XR2 XR3 XR4 XR5 ⟨1, by decide⟩ := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xr2 : EV3 A3 A3I (hsGenWords.getD (⟨2, by decide⟩ : Fin 6).val []) =
    sel6 XR0 XR1 XR2 XR3 XR4 XR5 ⟨2, by decide⟩ := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xr3 : EV3 A3 A3I (hsGenWords.getD (⟨3, by decide⟩ : Fin 6).val []) =
    sel6 XR0 XR1 XR2 XR3 XR4 XR5 ⟨3, by decide⟩ := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xr4 : EV3 A3 A3I (hsGenWords.getD (⟨4, by decide⟩ : Fin 6).val []) =
    sel6 XR0 XR1 XR2 XR3 XR4 XR5 ⟨4, by decide⟩ := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xr5 : EV3 A3 A3I (hsGenWords.getD (⟨5, by decide⟩ : Fin 6).val []) =
    sel6 XR0 XR1 XR2 XR3 XR4 XR5 ⟨5, by decide⟩ := Nat.eq_of_beq_eq_true (by quickRfl)

set_option maxHeartbeats 0 in
theorem xinv : (List.finRange 6).all (fun j => inv3 (sel6 XR0 XR1 XR2 XR3 XR4 XR5 j) (sel6 XR0 XR1 XR2 XR3 XR4 XR5 j)) = true := by quickRfl

theorem xb0 : ck3Body ⟨0, by decide⟩ (sel6 XR0 XR1 XR2 XR3 XR4 XR5) (fxR ⟨0, by decide⟩) = true := by quickRfl

theorem xb1 : ck3Body ⟨1, by decide⟩ (sel6 XR0 XR1 XR2 XR3 XR4 XR5) (fxR ⟨1, by decide⟩) = true := by quickRfl

theorem xb2 : ck3Body ⟨2, by decide⟩ (sel6 XR0 XR1 XR2 XR3 XR4 XR5) (fxR ⟨2, by decide⟩) = true := by quickRfl

theorem xb3 : ck3Body ⟨3, by decide⟩ (sel6 XR0 XR1 XR2 XR3 XR4 XR5) (fxR ⟨3, by decide⟩) = true := by quickRfl

theorem xall : (List.finRange 4).all (fun i => strictB (fxR i) fun R => ck3Body i (sel6 XR0 XR1 XR2 XR3 XR4 XR5) R) = true :=
  finRange4_allR _ (by rw [strictB_eqR]; exact xb0) (by rw [strictB_eqR]; exact xb1)
    (by rw [strictB_eqR]; exact xb2) (by rw [strictB_eqR]; exact xb3)

theorem xbody : bAnd((List.finRange 6).all (fun j => inv3 (sel6 XR0 XR1 XR2 XR3 XR4 XR5 j) (sel6 XR0 XR1 XR2 XR3 XR4 XR5 j)),
    (List.finRange 4).all fun i => strictB (fxR i) fun R => ck3Body i (sel6 XR0 XR1 XR2 XR3 XR4 XR5) R) = true := by
  rw [xinv, xall]

theorem ok27020R : ck27020R = true := by
  unfold ck27020R
  refine bindGlue A3 A3I (fun A AI j => EV3 A AI (hsGenWords.getD j.val []))
    (fun X => bAnd((List.finRange 6).all (fun j => inv3 (X j) (X j)),
      (List.finRange 4).all fun i => strictB (fxR i) fun R => ck3Body i X R))
    (sel6 XR0 XR1 XR2 XR3 XR4 XR5) (fun j => ?_) xbody
  match j with
  | ⟨0, _⟩ => exact xr0
  | ⟨1, _⟩ => exact xr1
  | ⟨2, _⟩ => exact xr2
  | ⟨3, _⟩ => exact xr3
  | ⟨4, _⟩ => exact xr4
  | ⟨5, _⟩ => exact xr5

end CFSG.KD.TwoHS

end
