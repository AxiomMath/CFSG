module

public import Certificates.Kernel.YoshQ.Bound
public import CFSG.Certificates.Kernel.CosetW.Sound

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.CosetTable CFSG.EvenSporadicStandard.M12Std.Yosh

theorem card_split {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap i s : ℕ}
    (hi : subsetCheck ws S cap i = true)
    (hs : subsetCheck (restrictWords (subsetOf m S) ws) [] cap s = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ i * s := by
  obtain ⟨hf, hle⟩ := card_le_of_subsetCheck_nil _ hs
  obtain ⟨h1, h2⟩ := card_le_of_subsetCheck ws S hi
  exact ⟨h1, h2.trans (Nat.mul_le_mul_left i hle)⟩

theorem sub4 : subsetCheck (restrictWords (subsetOf 8 six) (rel4 0 0)) [] 20000 384 = true := by
  rw [subsetCheck_eq_checkW _ _ (by decide)]
  exact b4r

theorem rel4_card (α β : ℕ) (hα : α < 2) (hβ : β < 2) :
    Finite (PG 8 (rel4 α β)) ∧ Nat.card (PG 8 (rel4 α β)) ≤ 1536 := by
  have hb : ∀ ws : List (List (Fin 8 × Bool)),
      restrictWords (subsetOf 8 six) ws = restrictWords (subsetOf 8 six) (rel4 0 0) →
      checkW (mkParamsW (2 * 8) (invArrW 8) (CFSG.Certificates.CosetEnumeration.codes ws)
        (CFSG.Certificates.CosetEnumeration.codes ((subsetOf 8 six).map fun x => [(x, true)])))
        20000 4 = true →
      Finite (PG 8 ws) ∧ Nat.card (PG 8 ws) ≤ 1536 := by
    intro ws he hw
    have hi : subsetCheck ws six 20000 4 = true := by
      rw [subsetCheck_eq_checkW _ _ (by decide)]
      exact hw
    have hs : subsetCheck (restrictWords (subsetOf 8 six) ws) [] 20000 384 = true := by
      rw [he]
      exact sub4
    exact card_split ws six hi hs
  interval_cases α <;> interval_cases β
  · exact hb _ rfl b4.1
  · exact hb _ b4eq.1 b4.2.1
  · exact hb _ b4eq.2.1 b4.2.2.1
  · exact hb _ b4eq.2.2 b4.2.2.2

theorem relE_card : Finite (PG 6 relE) ∧ Nat.card (PG 6 relE) ≤ 128 := by
  apply card_le_of_subsetCheck_nil (cap := 20000)
  rw [subsetCheck_eq_checkW _ _ (by decide)]
  exact bE

theorem subN : subsetCheck (restrictWords (subsetOf 9 six) (relN 0 0 0)) [] 20000 128 = true := by
  rw [subsetCheck_eq_checkW _ _ (by decide)]
  exact bNr

theorem relN_card (α k : ℕ) (hα : α < 2) (hk : k < 2) :
    Finite (PG 9 (relN α α k)) ∧ Nat.card (PG 9 (relN α α k)) ≤ 3072 := by
  have hb : ∀ ws : List (List (Fin 9 × Bool)),
      restrictWords (subsetOf 9 six) ws = restrictWords (subsetOf 9 six) (relN 0 0 0) →
      checkW (mkParamsW (2 * 9) (invArrW 9) (CFSG.Certificates.CosetEnumeration.codes ws)
        (CFSG.Certificates.CosetEnumeration.codes ((subsetOf 9 six).map fun x => [(x, true)])))
        20000 24 = true →
      Finite (PG 9 ws) ∧ Nat.card (PG 9 ws) ≤ 3072 := by
    intro ws he hw
    have hi : subsetCheck ws six 20000 24 = true := by
      rw [subsetCheck_eq_checkW _ _ (by decide)]
      exact hw
    have hs : subsetCheck (restrictWords (subsetOf 9 six) ws) [] 20000 128 = true := by
      rw [he]
      exact subN
    exact card_split ws six hi hs
  interval_cases α <;> interval_cases k
  · exact hb _ rfl bN.1
  · exact hb _ bNeq.1 bN.2.1
  · exact hb _ bNeq.2.1 bN.2.2.1
  · exact hb _ bNeq.2.2 bN.2.2.2

end CertificateChecks.KernelYoshQ

end
