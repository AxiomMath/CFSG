module

public import Certificates.Kernel.He.Words
public import CFSG.Certificates.Kernel.Bounds.J3Alt.RelsTC
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelJ3

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE TauCeti
open CertificateChecks.KernelHe

theorem relatorLetters_ent : Sporadic.j3Presentation.relatorLetters.map HeB.ent = J3A.list := by
  rw [J3A.rels_eq]
  decide

theorem letters_small : ∀ w ∈ Sporadic.j3Presentation.relatorLetters,
    w.length < 1024 ∧ ∀ l ∈ w, l.1 < 127 := by
  rw [J3A.rels_eq]
  decide

theorem rel_eq (r : ℕ) : J3A.rel r = J3A.list.getD r 0 := by
  rcases Nat.lt_or_ge r 8 with h | h
  · interval_cases r <;> rfl
  · have e : ∀ k < 8, Nat.beq r k = false := fun k hk =>
      Bool.eq_false_iff.mpr (fun hc => by rw [Nat.beq_eq] at hc; omega)
    simp only [J3A.rel, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [J3A.list]; omega)]
    rfl

theorem rel_ok (r : ℕ) :
    wWord (J3A.rel r) < 2 ^ (8 * wLen (J3A.rel r)) ∧
      bval (KB.tcGen Sporadic.j3Presentation) (wWord (J3A.rel r)) (wLen (J3A.rel r)) = 1 := by
  rw [rel_eq, ← relatorLetters_ent, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hw : Sporadic.j3Presentation.relatorLetters[r]? with _ | w
  · exact ⟨by decide, rfl⟩
  · have hmem := List.mem_of_getElem? hw
    obtain ⟨hlen, hl⟩ := letters_small w hmem
    simp only [Option.map_some, Option.getD_some]
    rw [wWord_ent w hlen, wLen_ent w hlen]
    exact ⟨wordNat_lt w hl, (bval_wordNat _ w hl).trans (KB.sword_relatorLetters _ w hmem)⟩

end CertificateChecks.KernelJ3

end
