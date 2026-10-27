module

public import Certificates.Kernel.ONCover.Dce.Data
public import Certificates.Data.Kernel.TwistDce2.Defs

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce2

@[expose] noncomputable def belowB (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih a => wBelow 12 (RW a) && ih (a + 1)) n

theorem belowB_sound : ∀ n a, belowB n a = true → ∀ r < n, wBelow 12 (RW (a + r)) = true
  | 0, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, a, h, r, hr => by
    have h' : (wBelow 12 (RW a) && belowB n (a + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases r with _ | r
    · exact h'.1
    · have e := belowB_sound n (a + 1) h'.2 r (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at e

theorem below_ok : belowB 18934 0 = true := by
  decide +kernel

theorem rw_below : ∀ r < 18934, wBelow 12 (RW r) = true := by
  intro r hr
  have e := belowB_sound 18934 0 below_ok r hr
  rwa [Nat.zero_add] at e

end CFSG.KD.ONCoverDce3

end
