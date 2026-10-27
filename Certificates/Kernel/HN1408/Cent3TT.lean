module

public import Certificates.Kernel.HN1408.Cent3Inv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts3

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

noncomputable abbrev vH : Fin 5 → ↥P1408 := ![pA, pZ, pA * pZ, pB, pZ₁]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem cC_le : cC ≤ P1408 := by
  refine (closure_le _).2 ?_
  rintro _ ⟨w, -, rfl⟩
  exact elemW_mem w

theorem repC_tgt {t : Nat} (ht : t < 5) : RepC (tgtK t) ((vH ⟨t, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) := by
  interval_cases t
  · have e1 : tgtK 0 = WK wordA := rfl
    have e2 : ((vH ⟨0, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordA := rfl
    rw [e1, e2]
    exact repC_word (by decide)
  · have e1 : tgtK 1 = WK wordZ := rfl
    have e2 : ((vH ⟨1, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordZ := rfl
    rw [e1, e2]
    exact repC_word (by decide)
  · have e1 : tgtK 2 = pc (WK wordA) (WK wordZ) := rfl
    have e2 : ((vH ⟨2, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordA * elemW wordZ := rfl
    rw [e1, e2]
    exact repC_pc (repC_word (by decide)) (repC_word (by decide))
  · have e1 : tgtK 3 = WK wordB := rfl
    have e2 : ((vH ⟨3, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordB := rfl
    rw [e1, e2]
    exact repC_word (by decide)
  · have e1 : tgtK 4 = WK wordZ₁ := rfl
    have e2 : ((vH ⟨4, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordZ₁ := rfl
    rw [e1, e2]
    exact repC_word (by decide)

theorem repK_parts {RK RT : Nat → Nat} {RW : List (List Nat)} {c : Nat}
    (h : repK RK RT RW c = true) : RK c < 1440 ∧ RT c < 5 ∧ lettersOK (RW.getD c []) = true ∧
      pc (WK (RW.getD c [])) (tgtK (RT c)) = pc (elK (RK c)) (WK (RW.getD c [])) := by
  unfold repK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, c, Nat.eq_of_beq_eq_true d⟩

@[expose] noncomputable def elH {k : Nat} (hk : k < 1440) : ↥P1408 := ⟨el k, cC_le (el_mem hk)⟩

theorem elH_val {k : Nat} (hk : k < 1440) : ((elH hk : ↥P1408) : Equiv.Perm (Fin 1408)) = el k :=
  rfl

theorem rep_conj {c : Nat} (hc : c < 6) :
    ∃ (hk : RK c < 1440) (ht : RT c < 5), IsConj (vH ⟨RT c, ht⟩) (elH hk) := by
  obtain ⟨hk, ht, hl, he⟩ := repK_parts (allN_spec ch441603_rep c hc)
  refine ⟨hk, ht, isConj_iff.2 ⟨⟨elemW (RW.getD c []), elemW_mem _⟩, Subtype.ext ?_⟩⟩
  have h1 := repC_pc (repC_word hl) (repC_tgt ht)
  have h2 := repC_pc (repC_el hk) (repC_word hl)
  rw [he] at h1
  have e := eq_of_repC h1 h2
  change elemW (RW.getD c []) * ((vH ⟨RT c, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) *
    (elemW (RW.getD c []))⁻¹ = el (RK c)
  rw [e, mul_inv_cancel_right]

variable (hC : Nat.card cC = 1440)
include hC

theorem inv_conj {y : ↥P1408} (hyC : (y : Equiv.Perm (Fin 1408)) ∈ cC) (hy2 : y ^ 2 = 1)
    (hy1 : y ≠ 1) : ∃ k < 1440, (y : Equiv.Perm (Fin 1408)) = el k ∧ R k ≠ 0 ∧
      ∃ ht : RT ((R k - 1) % 8) < 5, IsConj (vH ⟨RT ((R k - 1) % 8), ht⟩) y := by
  obtain ⟨k, hk, hyk⟩ := exists_el hC hyC
  have hi : el k * el k = 1 ∧ el k ≠ 1 := by
    refine ⟨?_, fun e => hy1 (Subtype.ext (by rw [hyk, e]; rfl))⟩
    rw [← hyk, ← pow_two]
    exact congrArg Subtype.val hy2
  have h0 : R k ≠ 0 := fun h0 => row_zero hC hk h0 hi
  obtain ⟨hc6, c', hc', he⟩ := row_conj hC hk h0
  obtain ⟨hr, ht, hconj⟩ := rep_conj hc6
  refine ⟨k, hk, hyk, h0, ht, hconj.trans (isConj_iff.2 ⟨elH hc', Subtype.ext ?_⟩)⟩
  change el c' * el (RK ((R k - 1) % 8)) * (el c')⁻¹ = (y : Equiv.Perm (Fin 1408))
  rw [he, hyk, mul_inv_cancel_right]

omit hC in
theorem ttK_eq {v : Nat} (hv : v ≠ 0) :
    ttK RT v = if RT ((v - 1) % 8) = 0 ∨ RT ((v - 1) % 8) = 2 ∨ RT ((v - 1) % 8) = 4 then 1
      else 0 := by
  unfold ttK
  have e : Nat.beq v 0 = false := Bool.eq_false_iff.2 fun h => hv (Nat.eq_of_beq_eq_true h)
  rw [e]
  change CFSG.KC.Loop.strictN (RT ((v - 1) % 8)) _ = _
  rw [strictN_eq']
  generalize RT ((v - 1) % 8) = t
  simp only [nIf_ite, Nat.beq_eq]
  split_ifs <;> omega

omit hC in
theorem ttK_le (v : Nat) : ttK RT v ≤ 1 := by
  by_cases hv : v = 0
  · subst hv
    exact Nat.zero_le _
  · rw [ttK_eq hv]
    split_ifs <;> omega

theorem tTH_iff (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j)) {y : ↥P1408} {k : Nat}
    (h0 : R k ≠ 0) (ht : RT ((R k - 1) % 8) < 5)
    (hconj : IsConj (vH ⟨RT ((R k - 1) % 8), ht⟩) y) :
    tTH pA pZ pZ₁ y ↔ ttK RT (R k) = 1 := by
  have key : ∀ i : Fin 5, IsConj y (vH i) ↔ i = ⟨RT ((R k - 1) % 8), ht⟩ := fun i => by
    constructor
    · intro h
      by_contra hne
      exact hnc _ _ (Ne.symm hne) (hconj.trans h)
    · rintro rfl
      exact hconj.symm
  have ea : pA = vH 0 := rfl
  have ez : pA * pZ = vH 2 := rfl
  have e1 : pZ₁ = vH 4 := rfl
  unfold tTH
  rw [ez, ea, e1, key, key, key, ttK_eq h0]
  have v0 : ((0 : Fin 5) : Nat) = 0 := rfl
  have v2 : ((2 : Fin 5) : Nat) = 2 := rfl
  have v4 : ((4 : Fin 5) : Nat) = 4 := rfl
  simp only [Fin.ext_iff, v0, v2, v4]
  generalize RT ((R k - 1) % 8) = t
  by_cases hh : t = 0 ∨ t = 2 ∨ t = 4
  · rw [if_pos hh]
    exact ⟨fun _ => rfl, fun _ => by rcases hh with h | h | h <;> simp [h]⟩
  · rw [if_neg hh]
    exact ⟨fun h => absurd (by rcases h with h | h | h <;> simp [← h]) hh,
      fun h => absurd h (by norm_num)⟩

omit hC in
theorem cntN_eq (n : Nat) :
    cntN R RT n = ((Finset.range n).filter fun k => ttK RT (R k) = 1).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : cntN R RT (n + 1) = cntN R RT n + ttK RT (R n) := by
      change CFSG.KC.Loop.strictN (cntN R RT n) (fun a => Nat.add a (ttK RT (R n))) = _
      rw [strictN_eq']
      rfl
    rw [e, ih, Finset.range_add_one, Finset.filter_insert]
    have hle := ttK_le (R n)
    by_cases h1 : ttK RT (R n) = 1
    · rw [if_pos h1, Finset.card_insert_of_notMem (by simp), h1]
    · rw [if_neg h1]
      omega

end CFSG.KD.HN1408.Cent3

end
