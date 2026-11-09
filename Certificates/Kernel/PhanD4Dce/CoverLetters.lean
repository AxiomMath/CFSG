module

public import Certificates.Kernel.PhanD4Dce.Data
public import Certificates.Kernel.PhanD4Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

@[expose] noncomputable def letterOK (c : Nat) : Bool :=
  CFSG.KC.andB (Nat.blt (CFSG.KC.TwDce2.ivL INVM c) 12)
    (Nat.rec (motive := fun _ => Bool) true
      (fun x acc2 => CFSG.KC.andB acc2
        (CFSG.KC.TwDce.sB (CFSG.KC.YModel.fieldAt 15 (FO c) x) (fun y =>
          CFSG.KC.andB (Nat.blt y 22680)
            (Nat.beq (CFSG.KC.YModel.fieldAt 15 (FO (CFSG.KC.TwDce2.ivL INVM c)) y) x)))) 22680)

theorem natRec_all_of {g : Nat → Bool} : ∀ {n : Nat}, (∀ c < n, g c = true) →
    Nat.rec (motive := fun _ => Bool) true (fun c acc => CFSG.KC.andB acc (g c)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    have h1 := natRec_all_of (g := g) (n := n) (fun c hc => h c (by omega))
    have h2 := h n (by omega)
    show CFSG.KC.andB _ (g n) = true
    rw [h1, h2] <;> rfl

set_option maxRecDepth 200000 in
theorem omega_letter0 : letterOK 0 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter1 : letterOK 1 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter2 : letterOK 2 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter3 : letterOK 3 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter4 : letterOK 4 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter5 : letterOK 5 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter6 : letterOK 6 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter7 : letterOK 7 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter8 : letterOK 8 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter9 : letterOK 9 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter10 : letterOK 10 = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem omega_letter11 : letterOK 11 = true := by
  decide +kernel

theorem omega_letters : lettersOK 15 FO INVM 12 22680 = true :=
  natRec_all_of (g := letterOK) (n := 12) fun c hc => match c, hc with
    | 0, _ => omega_letter0
    | 1, _ => omega_letter1
    | 2, _ => omega_letter2
    | 3, _ => omega_letter3
    | 4, _ => omega_letter4
    | 5, _ => omega_letter5
    | 6, _ => omega_letter6
    | 7, _ => omega_letter7
    | 8, _ => omega_letter8
    | 9, _ => omega_letter9
    | 10, _ => omega_letter10
    | 11, _ => omega_letter11
    | n + 12, h => absurd h (by omega)

end CFSG.KD.PhanD4Dce

end
