module

public import CFSG.Certificates.Kernel.F4MatSound
public import CFSG.Monster.B.Classical.UnitarySixBeta

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.F4M CFSG.KLie.CT CFSG.Fischer Matrix CFSG.Monster.B.Classical.UnitarySix
  CFSG.LieType.Universal.Unitary

theorem mul_of {P Q R : Nat} (h : Nat.beq (mmul P Q) R = true) : decM P * decM Q = decM R := by
  rw [← decM_mmul, Nat.eq_of_beq_eq_true h]

theorem det_of {P : Nat} (h : Nat.beq (det P) 1 = true) : (decM P).det = 1 := by
  rw [det_sound, Nat.eq_of_beq_eq_true h]
  rfl

theorem bar_eq : (bar : F4 → F4) = fun a => a ^ 2 := rfl

theorem unitary_of {P : Nat} (h : unitaryOK P = true) :
    ((decM P).map bar)ᵀ * antidiag 6 * decM P = antidiag 6 := by
  rw [bar_eq, ← decM_barM, ← decM_trn, ← decM_ANTI, ← decM_mmul, ← decM_mmul,
    Nat.eq_of_beq_eq_true h]

theorem trace_ne_of {P : Nat} (h : notB (Nat.beq (tr P) (sqC (tr P))) = true) :
    (decM P).trace ≠ bar (decM P).trace := by
  obtain ⟨ht, hlt⟩ := tr_sound P
  rw [bar_eq, ht]
  change cF4 (tr P) ≠ cF4 (tr P) ^ 2
  rw [cF4_sq hlt]
  have hsq : sqC (tr P) < 4 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 3 < 4)
  refine cF4_ne hlt hsq ?_
  cases hb : Nat.beq (tr P) (sqC (tr P))
  · rfl
  · rw [hb] at h
    exact absurd h (by decide)

theorem betaM_eq (P : Nat) : betaM (decM P) = decM (barM P) := by
  rw [decM_barM]
  rfl

end CertificateChecks.KernelTwoE6

end
