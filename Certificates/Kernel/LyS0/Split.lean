module

public import Certificates.Kernel.LyS0.Each

public section

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0 CFSG.KC.Enum

theorem allBlk_spec' {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    allBlk b f len = true → ∀ l < len, f (Nat.add b l) = true
  | 0, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true at h
    cases hf : f (Nat.add b len)
    · rw [hf] at h
      change false = true at h
      cases h
    · rw [hf] at h
      change allBlk b f len = true at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact allBlk_spec' h l hl
      · exact hf

theorem allBlk_intro' {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_intro' fun l hl => h l (by omega)]

theorem allBlk_join {b : Nat} {f : Nat → Bool} {a c : Nat} (h1 : allBlk b f a = true)
    (h2 : allBlk (Nat.add b a) f c = true) : allBlk b f (Nat.add a c) = true := by
  apply allBlk_intro'
  intro l hl
  by_cases hla : l < a
  · exact allBlk_spec' h1 l hla
  · have h := allBlk_spec' h2 (l - a) (by simp only [Nat.add_eq] at hl; omega)
    have e : Nat.add (Nat.add b a) (l - a) = Nat.add b l := by simp only [Nat.add_eq]; omega
    rw [e] at h
    exact h

@[expose] noncomputable def leftCA (q : Nat) : Bool := leftK GI T (Nat.mul 81 q) 41

@[expose] noncomputable def leftCB (q : Nat) : Bool := leftK GI T (Nat.add (Nat.mul 81 q) 41) 40

theorem leftC_of (q : Nat) (ha : leftCA q = true) (hb : leftCB q = true) : leftC q = true := by
  unfold leftCA leftK at ha
  unfold leftCB leftK at hb
  unfold leftC leftK
  exact allBlk_join (a := 41) (c := 40) ha hb

end CertificateChecks.KernelLyS0

end
