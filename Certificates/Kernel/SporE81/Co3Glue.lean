module

public import Certificates.Kernel.SporE81.Co3Checks
public import CFSG.Certificates.Kernel.E81KSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CertificateChecks.KernelE81.Co3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum CFSG.KC.E81K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Sporadic.Schreier.Co3
open CertificateChecks.KernelE81 CertificateChecks.KernelSpor

theorem hw9 : szOK 276 9 = true := by quickRfl

theorem eq_of_beq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem pgE : ∀ j < 2, co3E81.pg[j]! = unpack 276 9 (Co3C.S j) := by
  intro j hj
  rw [← Co3C.binds.2.2.2.2.1 j (by omega)]
  interval_cases j
  · simp [co3E81]
  · simp [co3E81]

@[expose] noncomputable def pinQ : Pin 276 9 co3E81.qKeys :=
  ⟨C3Q.ng, C3Q.N, C3Q.G, C3Q.T, C3Q.E, C3Q.S, C3Q.SK, C3Q.ok, keysQ⟩

@[expose] noncomputable def pinR : Pin 276 9 co3E81.rKeys :=
  ⟨C3R.ng, C3R.N, C3R.G, C3R.T, C3R.E, C3R.S, C3R.SK, C3R.ok, keysR⟩

@[expose] noncomputable def pinD : Pin 276 9 co3E81.dKeys :=
  ⟨C3D.ng, C3D.N, C3D.G, C3D.T, C3D.E, C3D.S, C3D.SK, C3D.ok, keysD⟩

theorem dsize : co3E81.dW.size = 1 := by simp [co3E81]

theorem zOK' : pm (C3Z 0) (pm (C3Z 0) (C3Z 0)) = pidn 276 9 ∧ C3Z 0 ≠ pidn 276 9 ∧
    pm (C3Z 0) (C3Z 0) = C3Z 1 ∧ ∀ k < 4, pm (C3Z 0) (C3Q.G k) = pm (C3Q.G k) (C3Z 0) := by
  have h := zOK
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨eq_of_beq h1, fun e => ?_, eq_of_beq h3, fun k hk => eq_of_beq (allN_spec h4 k hk)⟩
  rw [e, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem e81Check_true : e81Check co3E81 = true := by
  refine e81Check_of_pins hw9 co3E81 rfl (mp := 2) Co3C.S (by simp [co3E81]) pgE (allN_spec perm)
    rfl pinQ pinR (fun _ => pinD) (nh := 10) C3H (C3Z 0) lettersQ lettersH lettersZ lettersR
    lettersD wordsQ rfl (by decide) wordZ zOK'.1 zOK'.2.1 zOK'.2.2.2 wordsR rfl (by decide)
    (by decide) ?_ (fun _ _ => ⟨by decide, by decide⟩) ?_ wordsH ?_
  · intro t ht
    rw [dsize] at ht
    obtain rfl : t = 0 := by omega
    exact wordsD
  · intro t _ a ha
    have h := allN_spec elem a ha
    rw [Bool.and_eq_true] at h
    exact ⟨eq_of_beq h.1, fun b hb => eq_of_beq (allN_spec h.2 b hb)⟩
  · intro k hk
    rw [dsize]
    exact cov_of zOK'.2.2.1 (allN_spec zw) (allN_spec cov k hk)

end CertificateChecks.KernelE81.Co3K

end
