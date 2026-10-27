
module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.InvFixChk
public import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.BfsPin CFSG.EvenSporadicStandard.HNRecog

theorem fixN_eq_length (X : Nat) :
    fixN X = ((List.range 1408).filter fun x => Nat.beq (pt X x) x).length := by
  unfold fixN
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  induction (List.range 1408) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases Nat.beq (pt X x) x <;> rfl

theorem fix_none {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (h : fixN X = 0) :
    ∀ x : Fin 1408, g x ≠ x := by
  intro x hx
  rw [fixN_eq_length, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  have h1 := h x.val (List.mem_range.2 x.2)
  rw [repC_pt hX x.2, Fin.eta, hx] at h1
  exact h1 (Nat.beq_refl _)

theorem fix_some {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (h : 0 < fixN X) :
    ∃ x : Fin 1408, g x = x := by
  rw [fixN_eq_length] at h
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h
  rw [List.mem_filter, List.mem_range] at hx
  refine ⟨⟨x, hx.1⟩, Fin.ext ?_⟩
  rw [← repC_pt hX hx.1]
  exact Nat.eq_of_beq_eq_true hx.2

theorem fix_counts :
    fixN (WK wordA) = 0 ∧ fixN (WK wordZ) = 0 ∧ fixN (pc (WK wordZ) (WK wordA)) = 128 ∧
      fixN (pc (WK wordA) (WK wordZ)) = 128 ∧
      fixN (pc (pc (WK wordA) (WK wordZ)) (WK wordA)) = 0 ∧ fixN (WK wordB) = 0 ∧
      fixN (pc (WK wordB) (WK wordA)) = 0 ∧ fixN (WK wordZ₁) = 0 ∧
      fixN (pc (WK wordZ₁) (WK wordA)) = 0 := by
  have h := fix_ok
  unfold fixK fixPair at h
  simp only [strictB_app, bAnd_iff] at h
  obtain ⟨h1, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, a5, b5⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true b2,
    Nat.eq_of_beq_eq_true a3, Nat.eq_of_beq_eq_true b3, Nat.eq_of_beq_eq_true a4,
    Nat.eq_of_beq_eq_true b4, Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true b5⟩

theorem z_no_fix : ∀ x : Fin 1408, elemZ x ≠ x :=
  fix_none (repC_word (w := wordZ) (by decide)) fix_counts.2.1

theorem az_fix : ∃ x : Fin 1408, (elemA * elemZ) x = x :=
  fix_some (repC_pc (repC_word (w := wordA) (by decide)) (repC_word (w := wordZ) (by decide)))
    (by rw [fix_counts.2.2.2.1]; norm_num)

theorem not_conj_z_az (c : Equiv.Perm (Fin 1408)) : c * elemZ * c⁻¹ ≠ elemA * elemZ := by
  intro he
  obtain ⟨x, hx⟩ := az_fix
  rw [← he, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hx
  exact z_no_fix (c⁻¹ x) (Equiv.Perm.eq_inv_iff_eq.2 hx)

end CFSG.KD.HN1408.CzInv

end
