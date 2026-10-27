module

public import Certificates.Kernel.Misc.Perm.A6Checks
public import CFSG.Certificates.Kernel.Misc.PermA6Sound
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.LocalQTPermSound
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CertificateChecks.KernelMisc.A6

open Equiv CFSG.KC.Misc.Clos CFSG.KC.Misc.A6 CFSG.KC.LQT CFSG.RankThree.Native.ONTriple

theorem hG : ∀ j < [sK1, sK2].length, G j = pcode ([sK1, sK2].getD j 1) := by
  decide +kernel

theorem codeY : ∀ j < 2, pcode (sY j) = YJ j := by decide +kernel

theorem codeV : ∀ j < 2, ∀ m < 3, ∀ i < 3, pcode (sV j m i) = W j (3 * m + i) := by
  decide +kernel

theorem card_closure : Nat.card (Subgroup.closure {g | g ∈ [sK1, sK2]}) = 360 :=
  ((clos_card_proved (pcode_enc_proved h6) [sK1, sK2] hG (by norm_num)
    ((CFSG.KC.Misc.Clos.allN_iff _ _).1 treeB) ((CFSG.KC.Misc.Clos.allN_iff _ _).1 sortB)).2.2
    ((CFSG.KC.Misc.Clos.allN_iff _ _).1 closedB)).1

theorem sign_sK : Perm.sign sK1 = 1 ∧ Perm.sign sK2 = 1 := by
  obtain ⟨h0, h1⟩ := P.andB_iff.1 evenB
  rw [hG 0 (by norm_num)] at h0
  rw [hG 1 (by norm_num)] at h1
  exact ⟨pcode_even h6 sK1 h0, pcode_even h6 sK2 h1⟩

theorem d1 (j : ℕ) (hj : j < 2) : ∀ t : Perm (Fin 6), Perm.sign t = 1 → t ^ 4 = 1 → t ≠ 1 →
    (∃ m < 3, ∃ i < 3, t = sV j m i) ∨ (cand1 (sY j) t).any (fun u => u ^ 4 != 1) :=
  d1K_sound (sY j) (sV j) (codeY j hj) (codeV j hj) ((P.allN_iff _ _).1 d1B j hj)

theorem d2 (j : ℕ) (hj : j < 2) (m : ℕ) (hm : m < 3) : ∀ s : Perm (Fin 6),
    Perm.sign s = 1 → s ^ 4 = 1 → s ≠ 1 → (∀ i < 3, s ≠ sV j m i) →
      (cand2 (sY j) s [1, sV j m 0, sV j m 1, sV j m 2]).any (fun u => u ^ 4 != 1) := by
  intro s h1 h2 h3 h4
  have hc := (P.allN_iff _ _).1 ((P.allN_iff _ _).1 d2B j hj) m hm
  exact d2K_sound _ _ _ _ (codeY j hj) (codeV j hj m hm 0 (by norm_num))
    (codeV j hj m hm 1 (by norm_num)) (codeV j hj m hm 2 (by norm_num)) hc s h1 h2 h3
    (h4 0 (by norm_num)) (h4 1 (by norm_num)) (h4 2 (by norm_num))

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple Equiv Equiv.Perm in
theorem facts : (Nat.card (Subgroup.closure {g | g ∈ [sK1, sK2]}) = 360)
    ∧ (Equiv.Perm.sign sK1 = 1 ∧ Equiv.Perm.sign sK2 = 1)
    ∧ (∀ j : ℕ, j < 2 → ∀ t : Perm (Fin 6), Equiv.Perm.sign t = 1 →
        t ^ 4 = 1 → t ≠ 1 →
          (∃ m < 3, ∃ i < 3, t = sV j m i) ∨ (cand1 (sY j) t).any (fun u => u ^ 4 != 1))
    ∧ (∀ j : ℕ, j < 2 → ∀ m : ℕ, m < 3 → ∀ s : Perm (Fin 6),
        Equiv.Perm.sign s = 1 → s ^ 4 = 1 → s ≠ 1 → (∀ i < 3, s ≠ sV j m i) →
          (cand2 (sY j) s [1, sV j m 0, sV j m 1, sV j m 2]).any (fun u => u ^ 4 != 1)) :=
  ⟨card_closure, sign_sK, d1, d2⟩

end CertificateChecks.KernelMisc.A6

end
