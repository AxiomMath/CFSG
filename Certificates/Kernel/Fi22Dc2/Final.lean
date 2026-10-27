module

public import Certificates.Kernel.Fi22Dc2.Glob
public import Certificates.Kernel.Fi22Dc2.Lets
public import Certificates.Kernel.Fi22Dc2.R1a
public import Certificates.Kernel.Fi22Dc2.R1b
public import Certificates.Kernel.Fi22Dc2.R2a
public import Certificates.Kernel.Fi22Dc2.R2b
public import Certificates.Kernel.Fi22Dc2.R2c
public import Certificates.Kernel.Fi22Dc2.R2d
public import Certificates.Kernel.Fi22Dc2.RT
public import Certificates.Kernel.Fi22Dc2.F0
public import Certificates.Kernel.Fi22Dc2.F1
public import CFSG.Assembly.Defs

public section

namespace CFSG.KD.Fi22Dc2

open CFSG.KC.SLD2

theorem of_shift {f g : Nat → Bool} {o c : Nat} (hf : ∀ i, f i = g (Nat.add o i))
    (h : ∀ i < c, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + c) : g i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem len_eq : D.bo.length = 2 ∧ D.R1.length = 45 ∧ D.roots.length = 73 := by
  have h := lens
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem bo_all :
    (List.range D.bo.length).all (fun i => borbOK C D (D.bo.getD i default)) = true := by
  rw [len_eq.1, List.all_eq_true]
  intro i hi
  have hi' : i < 2 := List.mem_range.1 hi
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · exact bo0
  · exact bo1

theorem r1_all :
    (List.range D.R1.length).all (fun c => rec1OK C D (D.R1.getD c default)) = true := by
  rw [len_eq.2.1, List.all_eq_true]
  intro i hi
  have hi' : i < 45 := List.mem_range.1 hi
  by_cases h : i < 15
  · exact of_shift (g := fun c => rec1OK C D (D.R1.getD c default)) (o := 0) (fun _ => rfl)
      R1a.all (by omega) (by omega)
  · exact of_shift (g := fun c => rec1OK C D (D.R1.getD c default)) (o := 15) (fun _ => rfl)
      R1b.all (by omega) (by omega)

theorem fr_all : (List.range C.nf).all (fRowOK C D) = true := by
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 5 := List.mem_range.1 hi
  by_cases h0 : i < 3
  · exact of_shift (g := fRowOK C D) (o := 0) (fun _ => rfl) F0.all (by omega) (by omega)
  · exact of_shift (g := fRowOK C D) (o := 3) (fun _ => rfl) F1.all (by omega) (by omega)

theorem r2_all : (List.range D.R1.length).all (rec2OK C D) = true := by
  rw [len_eq.2.1, List.all_eq_true]
  intro i hi
  have hi' : i < 45 := List.mem_range.1 hi
  by_cases h0 : i < 11
  · exact of_shift (g := rec2OK C D) (o := 0) (fun _ => rfl) R2a.all (by omega) (by omega)
  by_cases h1 : i < 22
  · exact of_shift (g := rec2OK C D) (o := 11) (fun _ => rfl) R2b.all (by omega) (by omega)
  by_cases h2 : i < 33
  · exact of_shift (g := rec2OK C D) (o := 22) (fun _ => rfl) R2c.all (by omega) (by omega)
  · exact of_shift (g := rec2OK C D) (o := 33) (fun _ => rfl) R2d.all (by omega) (by omega)

theorem rt_all : (List.range D.roots.length).all (rootsOK C D) = true := by
  rw [len_eq.2.2, List.all_eq_true]
  intro i hi
  exact RT.all i (List.mem_range.1 hi)

theorem dc2_ok : dc2Check C D = true := by
  unfold dc2Check
  rw [glob, bo_all, r1_all, frest, fr_all, r2_all, rt_all, ridx]
  rfl

theorem Q_lt : ∀ p < 3510, Q p < 3510 := by
  intro p hp
  have h0 := perm
  unfold permOK at h0
  have h := List.all_eq_true.1 h0 p (List.mem_range.2 hp)
  simp only [Bool.and_eq_true] at h
  exact Nat.blt_eq.mp h.1.1.2

open Certificates in
open CFSG.KD.Fi22Dc2 in
theorem facts :
    CFSG.KC.SLD2.dc2Check C D = true ∧ permOK = true ∧
    (∀ j < 9, ∀ p < 3510, P (((CFSG.Monster.B.Fischer.fi22OuterStrong3510 4)[j]!)[Q p]!) =
      CFSG.KC.E64F.wordF L (tw j) p) ∧
    (∀ k < 2, ∀ p < 3510, L (5 + k) p = P ((CFSG.Monster.B.Fischer.fi22StrongArrs[k]!)[Q p]!)) ∧
    hwOK = true ∧ D.sep = [0, 1, 2, 3, 6, 4].map P :=
  ⟨dc2_ok, perm, lets_T Q_lt, lets_ab Q_lt, hwB, eq_of_beq sepB⟩

end CFSG.KD.Fi22Dc2

end
