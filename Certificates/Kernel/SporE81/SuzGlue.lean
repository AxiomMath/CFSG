module

public import Certificates.Kernel.SporE81.SuzChecks
public import CFSG.Certificates.Kernel.E81KSound
public import CFSG.Certificates.Kernel.E81IKSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE81.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum CFSG.KC.E81K
open CFSG.KC.E81IK (covI_of)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Sporadic.SuzOddCore
open CertificateChecks.KernelE81 CertificateChecks.KernelSpor

theorem hw11 : szOK 1782 11 = true := by quickRfl

theorem pgE : ∀ j < 2, suzE81.pg[j]! = unpack 1782 11 (PG j) := by
  intro j hj
  have e : suzE81.pg = #[b0Arr, b1Arr] := rfl
  rw [e]
  interval_cases j
  · exact Suz2306.b0Arr_eq
  · exact Suz2306.b1Arr_eq

theorem pgP : ∀ j < 2, permB 1782 11 (PG j) = true := by
  have h := perm
  rw [Bool.and_eq_true] at h
  intro j hj
  interval_cases j
  · exact h.1
  · exact h.2

@[expose] noncomputable def pinQ : Pin 1782 11 suzE81.qKeys :=
  ⟨S9Q.ng, S9Q.N, S9Q.G, S9Q.T, S9Q.E, S9Q.S, S9Q.SK, S9Q.ok, keysQ⟩

@[expose] noncomputable def pinR : Pin 1782 11 suzE81.rKeys :=
  ⟨S9Q.ng, S9Q.N, S9Q.G, S9Q.T, S9Q.E, S9Q.S, S9Q.SK, S9Q.ok, keysQ⟩

@[expose] noncomputable def pinD (t : ℕ) : Pin 1782 11 suzE81.dKeys :=
  match t with
  | 0 => ⟨S9D0.ng, S9D0.N, S9D0.G, S9D0.T, S9D0.E, S9D0.S, S9D0.SK, S9D0.ok, keysD0⟩
  | 1 => ⟨S9D1.ng, S9D1.N, S9D1.G, S9D1.T, S9D1.E, S9D1.S, S9D1.SK, S9D1.ok, keysD1⟩
  | 2 => ⟨S9D2.ng, S9D2.N, S9D2.G, S9D2.T, S9D2.E, S9D2.S, S9D2.SK, S9D2.ok, keysD2⟩
  | 3 => ⟨S9D3.ng, S9D3.N, S9D3.G, S9D3.T, S9D3.E, S9D3.S, S9D3.SK, S9D3.ok, keysD3⟩
  | 4 => ⟨S9D4.ng, S9D4.N, S9D4.G, S9D4.T, S9D4.E, S9D4.S, S9D4.SK, S9D4.ok, keysD4⟩
  | 5 => ⟨S9D5.ng, S9D5.N, S9D5.G, S9D5.T, S9D5.E, S9D5.S, S9D5.SK, S9D5.ok, keysD5⟩
  | 6 => ⟨S9D6.ng, S9D6.N, S9D6.G, S9D6.T, S9D6.E, S9D6.S, S9D6.SK, S9D6.ok, keysD6⟩
  | 7 => ⟨S9D7.ng, S9D7.N, S9D7.G, S9D7.T, S9D7.E, S9D7.S, S9D7.SK, S9D7.ok, keysD7⟩
  | 8 => ⟨S9D8.ng, S9D8.N, S9D8.G, S9D8.T, S9D8.E, S9D8.S, S9D8.SK, S9D8.ok, keysD8⟩
  | _ => ⟨S9D9.ng, S9D9.N, S9D9.G, S9D9.T, S9D9.E, S9D9.S, S9D9.SK, S9D9.ok, keysD9⟩

theorem pinD_eq : ∀ t < 10, (pinD t).ng = dNg t ∧ (pinD t).G = dG t ∧ (pinD t).N = dN t ∧
    (pinD t).T = dT t := by
  intro t ht
  interval_cases t <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem dsize : suzE81.dW.size = 10 := by simp [suzE81]

theorem zOK' : pm (S9Z 0) (pm (S9Z 0) (S9Z 0)) = pidn 1782 11 ∧ S9Z 0 ≠ pidn 1782 11 ∧
    pm (S9Z 0) (S9Z 0) = S9Z 1 ∧ ∀ k < 3, pm (S9Z 0) (S9Q.G k) = pm (S9Q.G k) (S9Z 0) := by
  have h := zOK
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun e => ?_, Nat.eq_of_beq_eq_true h3,
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h4 k hk)⟩
  rw [e, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem ppQ : ∀ k < S9Q.N, PP 1782 11 (S9Q.T k) :=
  PP_pts S9Q.ok fun k hk => ((words hw11 pgE pgP wordsQ lettersQ).2 k hk).2

theorem e81Check_true : e81Check suzE81 = true := by
  refine e81Check_of_pins hw11 suzE81 rfl (mp := 2) PG (by simp [suzE81]) pgE pgP
    rfl pinQ pinR pinD (nh := 1) (fun _ => pidn 1782 11) (S9Z 0) lettersQ lettersH
    lettersZ lettersR lettersD wordsQ rfl (by decide) wordZ zOK'.1 zOK'.2.1 zOK'.2.2.2 wordsR rfl
    (by decide) (by decide) ?_ ?_ ?_ wordsH ?_
  · intro t ht
    rw [dsize] at ht
    obtain ⟨hg, hG, -, -⟩ := pinD_eq t ht
    rw [hg, hG]
    exact wordsD t ht
  · intro t ht
    rw [dsize] at ht
    obtain ⟨-, -, hN, -⟩ := pinD_eq t ht
    have h := allN_spec dSize t ht
    rw [Bool.and_eq_true] at h
    rw [hN]
    exact ⟨Nat.le_of_ble_eq_true h.1, Nat.le_of_ble_eq_true h.2⟩
  · intro t ht a ha
    rw [dsize] at ht
    obtain ⟨hg, hG, -, -⟩ := pinD_eq t ht
    rw [hg] at ha
    rw [hG]
    have h := allN_spec (allN_spec elem t ht) a ha
    rw [Bool.and_eq_true] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1,
      fun b hb => Nat.eq_of_beq_eq_true (allN_spec h.2 b (by rwa [hg] at hb))⟩
  · intro k hk
    rcases covI_of hw11 (nh := 1) (H := fun _ => pidn 1782 11) Nat.one_pos rfl zOK'.2.2.1
      (ppQ k hk) (pp_of_permB hw11 permZ) (allN_spec cov k hk) with
      h | ⟨i, hi, t, ht, j, hj, j', hj', e1, e2⟩
    · exact Or.inl h
    · right
      obtain ⟨-, -, hN, hT⟩ := pinD_eq t ht
      refine ⟨i, hi, t, by rw [dsize]; exact ht, j, by rw [hN]; exact hj, j', by rw [hN]; exact hj',
        ?_, ?_⟩
      · rw [hT]
        exact e1
      · rw [hT]
        exact e2

end CertificateChecks.KernelE81.SuzK

end
