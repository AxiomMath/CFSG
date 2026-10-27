module

public import CFSG.CGT.M24R.N8Inputs
import CFSG.Certificates.Kernel.M24R.N8KSound
import CFSG.Certificates.Kernel.CosetW.Sound
import Certificates.Kernel.N8.Enum
import Certificates.Kernel.N8.Count
import Certificates.Kernel.N8.Words
public import Mathlib

public section

open CFSG.CosetTable CFSG.CGT.M24R CFSG.KC.N8K

namespace CertificateChecks.N8K

theorem relsN8Ten_bound : Finite (PG 10 relsN8Ten) ∧ Nat.card (PG 10 relsN8Ten) ≤ 322560 := by
  have hX : subsetCheck relsN8Ten [0, 1, 2, 3, 4, 5] 1000 16 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_enumX
  have h6 : subsetCheck carmR6 [0, 1, 2, 3, 4] 200 8 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_carm6
  have h5 : subsetCheck carmR5 [0, 1, 2, 3] 200 7 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_carm5
  have h4 : subsetCheck carmR4 [0, 1, 2] 200 6 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_carm4
  have h3 : subsetCheck carmR3 [0, 1] 200 5 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_carm3
  have h2 : subsetCheck carmR2 [0] 200 4 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_carm2
  have h1 : subsetCheck carmR1 [] 200 3 = true := by
    rw [subsetCheck_eq_checkW _ _ (by decide)]
    exact n8k_carm1
  obtain ⟨fA, cA⟩ := carm_card_le h6 h5 h4 h3 h2 h1
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheck relsN8Ten [0, 1, 2, 3, 4, 5] hX
  exact ⟨f2, (c2.trans (Nat.mul_le_mul_left _ cA)).trans (by norm_num)⟩

theorem proof21192 : (Finite (PG 10 relsN8Ten) ∧ Nat.card (PG 10 relsN8Ten) ≤ 322560) ∧
    glCountCheck = true ∧
    ∃ W : List (List (Fin 6)), W.length = 20160 ∧ (W.map evalM8).Nodup :=
  ⟨relsN8Ten_bound, glCount_of n8k_count, glWords_of n8k_words⟩

end CertificateChecks.N8K

end
