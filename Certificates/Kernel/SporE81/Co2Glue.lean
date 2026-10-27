module

public import Certificates.Kernel.SporE81.Co2Checks
public import Certificates.Kernel.Sporadic.Co2.Order
public import CFSG.Certificates.Kernel.E81KSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CertificateChecks.KernelE81.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum CFSG.KC.E81K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CertificateChecks.KernelE81 CertificateChecks.KernelSpor

theorem hw12 : szOK 2300 12 = true := by quickRfl

theorem eq_of_beq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem pgE : ∀ j < 2, co2E81.pg[j]! = unpack 2300 12 (Co2A.S j) := by
  intro j hj
  interval_cases j
  · simpa [co2E81] using Co2Order.a_eq 0 (by decide)
  · simpa [co2E81] using Co2Order.a_eq 1 (by decide)

@[expose] noncomputable def pinQ : Pin 2300 12 co2E81.qKeys :=
  ⟨C2Q.ng, C2Q.N, C2Q.G, C2Q.T, C2Q.E, C2Q.S, C2Q.SK, C2Q.ok, keysQ⟩

@[expose] noncomputable def pinR : Pin 2300 12 co2E81.rKeys := pinQ

@[expose] noncomputable def pinD : Pin 2300 12 co2E81.dKeys :=
  ⟨C2D.ng, C2D.N, C2D.G, C2D.T, C2D.E, C2D.S, C2D.SK, C2D.ok, keysD⟩

theorem dsize : co2E81.dW.size = 1 := by simp [co2E81]

theorem wordsH : co2E81.hW.toList.map (posWordK 2300 12 Co2A.S) = (List.range 16).map C2H := by
  have hc : ∀ k < 8, ∀ j < 2, Nat.beq (posWordK 2300 12 Co2A.S
      (co2E81.hW.toList.getD (2 * k + j) [])) (C2H (2 * k + j)) = true := by
    intro k hk j hj
    interval_cases k
    · exact allN_spec wordsH0 j hj
    · exact allN_spec wordsH1 j hj
    · exact allN_spec wordsH2 j hj
    · exact allN_spec wordsH3 j hj
    · exact allN_spec wordsH4 j hj
    · exact allN_spec wordsH5 j hj
    · exact allN_spec wordsH6 j hj
    · exact allN_spec wordsH7 j hj
  apply List.ext_getElem
  · rw [List.length_map, List.length_map, List.length_range, hWlen]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    have hlt : i < co2E81.hW.toList.length := by simpa using h1
    have e := hc (i / 2) (by rw [hWlen] at hlt; omega) (i % 2) (Nat.mod_lt _ (by decide))
    rw [Nat.div_add_mod] at e
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at e
    exact eq_of_beq e

theorem zOK' : pm (C2Z 0) (pm (C2Z 0) (C2Z 0)) = pidn 2300 12 ∧ C2Z 0 ≠ pidn 2300 12 ∧
    pm (C2Z 0) (C2Z 0) = C2Z 1 ∧ ∀ k < 3, pm (C2Z 0) (C2Q.G k) = pm (C2Q.G k) (C2Z 0) := by
  have h := zOK
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨eq_of_beq h1, fun e => ?_, eq_of_beq h3, fun k hk => eq_of_beq (allN_spec h4 k hk)⟩
  rw [e, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem e81Check_true : e81Check co2E81 = true := by
  refine e81Check_of_pins hw12 co2E81 rfl (mp := 2) Co2A.S (by simp [co2E81]) pgE (allN_spec perm)
    rfl pinQ pinR (fun _ => pinD) (nh := 16) C2H (C2Z 0) lettersQ lettersH lettersZ lettersR
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

end CertificateChecks.KernelE81.Co2K

end
