module

public import Certificates.Kernel.HS799102.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg)
open CFSG.KS (mask)

@[expose] noncomputable def imgMTB (w g m t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => cond (Nat.beq (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (nat_lit 1))
      (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w (mask w) g i))) acc) t

theorem testBit_eq_beq (m i : Nat) :
    Nat.testBit m i = Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1 := by
  have e1 : Nat.testBit m i = Nat.testBit (m >>> i) 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
  have e2 : Nat.land (Nat.shiftRight m i) 1 = (m >>> i) % 2 := Nat.and_one_is_mod _
  rw [e1, e2, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> rw [h] <;> rfl

theorem imgMT_eq_B (w g m : Nat) : ∀ t, imgMT w g m t = imgMTB w g m t
  | 0 => rfl
  | t + 1 => by
    show cond (Nat.testBit m t) (Nat.lor (imgMT w g m t) (Nat.shiftLeft 1 (pg w (mask w) g t)))
        (imgMT w g m t) =
      cond (Nat.beq (Nat.land (Nat.shiftRight m t) 1) 1)
        (Nat.lor (imgMTB w g m t) (Nat.shiftLeft 1 (pg w (mask w) g t))) (imgMTB w g m t)
    rw [imgMT_eq_B w g m t, testBit_eq_beq]

end CFSG.KC.PCent

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent

theorem ch799102_isr : setOrbK 100 7 hG 3 SM SR = true := by
  unfold setOrbK imgM
  simp only [imgMT_eq_B]
  quickRfl

end CertificateChecks.KernelHS799102

end
