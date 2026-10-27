module

public import Certificates.Kernel.PermCent.U43QuatGlue
public import Certificates.Kernel.PermCent.U43QuatRel

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.LieType.Multipliers.U43
  CertificateChecks.KernelPermCent.U43P1 Matrix

@[expose] noncomputable def s01E : Equiv.Perm (Fin 820) := perm820 (glK cS01)

@[expose] noncomputable def y0E : Equiv.Perm (Fin 820) := perm820 (glK cY0)

theorem perm820_smul {A B : GL (Fin 4) F9} {c : F9} (hc : c ≠ 0)
    (h : (A : Matrix (Fin 4) (Fin 4) F9) = c • (B : Matrix (Fin 4) (Fin 4) F9)) :
    perm820 A = perm820 B :=
  Equiv.ext fun i => Fin.ext (by
    have e : (c • (B : Matrix (Fin 4) (Fin 4) F9)) *ᵥ decode i =
        c • ((B : Matrix (Fin 4) (Fin 4) F9) *ᵥ decode i) := by
      exact Matrix.smul_mulVec c _ _
    rw [perm820_apply, perm820_apply, h, e, ptIndex_smul hc])

theorem pe_of_mat {A B : GL (Fin 4) F9}
    (h : (A : Matrix (Fin 4) (Fin 4) F9) = (B : Matrix (Fin 4) (Fin 4) F9)) :
    perm820 A = perm820 B :=
  congrArg perm820 (Units.ext h)

theorem det_s01 : (matK cS01).det ≠ 0 := by
  rw [quat_rels.2.1]
  decide

theorem det_y0 : (matK cY0).det ≠ 0 := by
  rw [quat_rels.2.2.2.1]
  decide

theorem s01E_mem : s01E ∈ psi.range :=
  perm820_mem_range (isUnitaryF_glK det_s01 quat_rels.1)
    (by rw [glK_val det_s01, quat_rels.2.1, uncode_three])

theorem y0E_mem : y0E ∈ psi.range :=
  perm820_mem_range (isUnitaryF_glK det_y0 quat_rels.2.2.1)
    (by rw [glK_val det_y0, quat_rels.2.2.2.1, uncode_three])

theorem val_q {j : ℕ} (hj : j < 14) :
    (glK (qc j) : Matrix (Fin 4) (Fin 4) F9) = matK (qc j) :=
  glK_val (qspec hj).1

theorem qE_eq' {j : ℕ} (hj : j < 14) : qE j = perm820 (glK (qc j)) := qE_eq hj

theorem neg_one_ne : (-1 : F9) ≠ 0 := by decide

theorem rel_perm :
    qE 0 * qE 0 = 1 ∧ qE 2 * qE 2 = qE 0 ∧ qE 1 * qE 2 * qE 1 = qE 2 ∧
      qE 3 * qE 4 * qE 3 = qE 4 ∧ qE 5 * qE 1 = qE 1 * qE 5 ∧ qE 5 * qE 2 = qE 2 * qE 5 ∧
      s01E * s01E = 1 ∧ s01E * qE 3 = qE 1 * s01E ∧ s01E * qE 4 = qE 2 * s01E ∧
      s01E * qE 1 = qE 3 * s01E ∧ s01E * qE 2 = qE 4 * s01E ∧ s01E * qE 0 = qE 0 * s01E ∧
      qE 7 * qE 0 = qE 0 * qE 7 ∧ y0E * (y0E * y0E) = 1 ∧ y0E * qE 5 = qE 5 * y0E ∧
      y0E * qE 1 = qE 2 * y0E ∧ y0E * qE 2 = qE 1 * qE 2 * y0E := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    -⟩ := quat_rels
  have v0 := val_q (j := 0) (by norm_num)
  have v1 := val_q (j := 1) (by norm_num)
  have v2 := val_q (j := 2) (by norm_num)
  have v3 := val_q (j := 3) (by norm_num)
  have v4 := val_q (j := 4) (by norm_num)
  have v5 := val_q (j := 5) (by norm_num)
  have v7 := val_q (j := 7) (by norm_num)
  have vs := glK_val det_s01
  have vy := glK_val det_y0
  have e0 := qE_eq' (j := 0) (by norm_num)
  have e1 := qE_eq' (j := 1) (by norm_num)
  have e2 := qE_eq' (j := 2) (by norm_num)
  have e3 := qE_eq' (j := 3) (by norm_num)
  have e4 := qE_eq' (j := 4) (by norm_num)
  have e5 := qE_eq' (j := 5) (by norm_num)
  have e7 := qE_eq' (j := 7) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e7, s01E, y0E, ← map_mul, ← map_one perm820]
  refine ⟨pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_,
    pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_,
    perm820_smul neg_one_ne ?_, perm820_smul neg_one_ne ?_, pe_of_mat ?_, pe_of_mat ?_,
    pe_of_mat ?_, pe_of_mat ?_⟩
  all_goals simp only [Units.val_mul, Units.val_one, v0, v1, v2, v3, v4, v5, v7, vs, vy]
  exacts [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem any_point {f g : ℕ → ℕ} (h : (List.range 820).any (fun i => !Nat.beq (f i) (g i)) = true) :
    ∃ i : Fin 820, f i ≠ g i := by
  obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 h
  refine ⟨⟨i, List.mem_range.1 hi⟩, fun e => ?_⟩
  have e' : f i = g i := e
  rw [e', Nat.beq_refl] at hne
  exact absurd hne (by decide)

theorem eK_q {j : ℕ} (hj : j < 14) (i : Fin 820) : (qE j i : ℕ) = imgK (qc j) false i := by
  rw [qE, gK, (quatEls_spec j hj).1]
  exact eK_apply (qspec hj).1 i

theorem y0E_apply (i : Fin 820) : (y0E i : ℕ) = imgK cY0 false i := by
  have e : y0E = eK cY0 false := by simp [y0E, eK]
  rw [e]
  exact eK_apply det_y0 i

theorem rel_ne : qE 0 ≠ 1 ∧ qE 5 * qE 4 ≠ qE 4 * qE 5 ∧ y0E * qE 1 ≠ qE 1 * y0E := by
  have h := quat_rels_ne
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨i, hi⟩ := any_point (g := id) h1
    apply hi
    rw [← eK_q (by norm_num), e]
    rfl
  · obtain ⟨i, hi⟩ := any_point h2
    apply hi
    have hv := eK_q (j := 4) (by norm_num) i
    have hd := eK_q (j := 5) (by norm_num) i
    rw [← hv, ← hd, ← eK_q (by norm_num), ← eK_q (by norm_num), ← Equiv.Perm.mul_apply,
      ← Equiv.Perm.mul_apply, e]
  · obtain ⟨i, hi⟩ := any_point h3
    apply hi
    rw [← eK_q (j := 1) (by norm_num), ← y0E_apply, ← y0E_apply, ← eK_q (by norm_num),
      ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, e]

theorem rel_gam : ∀ j < 6, qE (8 + j) * qE 1 = qE 1 * qE 0 * qE (8 + j) := by
  intro j hj
  have hg := quat_rels_gam
  rw [List.all_eq_true] at hg
  have h := of_decide_eq_true (hg j (List.mem_range.2 hj))
  rw [qE_eq' (by omega), qE_eq' (j := 1) (by norm_num), qE_eq' (j := 0) (by norm_num),
    ← map_mul, ← map_mul, ← map_mul]
  exact congrArg perm820 (Units.ext (by
    simp only [Units.val_mul, val_q (j := 8 + j) (by omega), val_q (j := 1) (by norm_num),
      val_q (j := 0) (by norm_num)]
    exact h))

end CertificateChecks.KernelPermCent.U43Quat

end
