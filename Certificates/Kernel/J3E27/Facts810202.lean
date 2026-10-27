module

public import CFSG.Sporadic.J3.Group
public import CFSG.Certificates.Kernel.TabMatGrpSound
public import Certificates.Kernel.J3E27.Chk810202

public section

namespace CertificateChecks.KernelJ3E27

open CFSG.KC.TabMatGrp CFSG.Sporadic.J3 CFSG.Sporadic.J3.Native CFSG.Certificates
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CertificateChecks.KernelLC.J3Ops

theorem MatP_A : MatP 80 SA.M = mA j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SA.bind, ← SA.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

theorem MatP_B : MatP 80 SB.M = mB j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SB.bind, ← SB.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

theorem dets : (mA j3Data).det ≠ 0 ∧ (mB j3Data).det ≠ 0 := by
  rw [← MatP_A, ← MatP_B]
  exact seedsK_det ch810202rel

theorem hA : MatP 80 SA.M = matOf (J j3Data).subtype (![a j3Data, b j3Data] 0) := by
  have e : (![a j3Data, b j3Data] 0 : J j3Data) = a j3Data := rfl
  rw [e, matOf, Subgroup.subtype_apply, coe_a, gA, dif_pos dets.1,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_A]

theorem hB : MatP 80 SB.M = matOf (J j3Data).subtype (![a j3Data, b j3Data] 1) := by
  have e : (![a j3Data, b j3Data] 1 : J j3Data) = b j3Data := rfl
  rw [e, matOf, Subgroup.subtype_apply, coe_b, gB, dif_pos dets.2,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_B]

theorem signedProd_toF2 {G : Type*} [Group G] (x y : G) (w : List (ℕ × Bool)) :
    signedProd ![x, y] (w.map toF2) = wordProd (img2 x y) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, signedProd_cons, ih]
    obtain ⟨g, e⟩ := l
    by_cases hg : g = 0 <;> simp [toF2, img2, hg, wordProd]

theorem wordProd_append' {G : Type*} [Group G] (x : ℕ → G) (u v : List (ℕ × Bool)) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp only [wordProd, List.map_append, List.prod_append]

theorem wordProd_invW' {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    wordProd x (J3E27.invW w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [wordProd, J3E27.invW]
  | cons l w ih =>
    have e : J3E27.invW (l :: w) = J3E27.invW w ++ [(l.1, !l.2)] := by
      simp [J3E27.invW]
    rw [e, wordProd_append', ih]
    obtain ⟨i, s⟩ := l
    cases s <;> simp [wordProd]

noncomputable def tau (i : Fin 4) : J j3Data := segVal ![a j3Data, b j3Data] segs i.val

theorem tau0 : tau 0 = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordW1 :=
  signedProd_toF2 _ _ _

theorem tau1 : tau 1 = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordX3 :=
  signedProd_toF2 _ _ _

theorem tau2 : tau 2 = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordS :=
  signedProd_toF2 _ _ _

theorem tau3 : tau 3 = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordT :=
  signedProd_toF2 _ _ _

theorem rels_one : ∀ q ∈ rels, signedProd tau q.1 = 1 := by
  intro q hq
  have h := grpK_sound (σ := ![a j3Data, b j3Data]) Subtype.val_injective hA hB segs
    (k := 4) (by decide) rels ch810202rel q hq
  have e : q.2 = [] := by
    simp only [rels, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rwa [e, signedProd_nil, mul_one] at h

theorem prods_ne {i j : ℕ} (hi : i < 27) (hj : j < 27) (hij : i ≠ j) :
    signedProd tau (prodW i) ≠ signedProd tau (prodW j) := by
  have h := distK_sound (σ := ![a j3Data, b j3Data]) (φ := (J j3Data).subtype) hA hB segs
    (k := 4) (by decide) prods ch810202dist i (by simpa [prods] using hi) j
    (by simpa [prods] using hj) hij
  simp only [prods, List.getElem_map, List.getElem_range] at h
  exact h

theorem signedProd_rep (k : ℕ) (w : List (Fin 4 × Bool)) :
    signedProd tau (rep k w) = signedProd tau w ^ k :=
  signedProd_replicate _ k w

theorem e27_facts : ∀ W₁ W₂ X₃ S T : J j3Data,
    W₁ = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordW1 →
    W₂ = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordW2 →
    X₃ = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordX3 →
    S = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordS →
    T = wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordT →
    W₁ ^ 3 = 1 ∧ W₂ ^ 3 = 1 ∧ X₃ ^ 3 = 1 ∧ W₁ * W₂ = W₂ * W₁ ∧ W₁ * X₃ = X₃ * W₁ ∧
      W₂ * X₃ = X₃ * W₂ ∧ S * W₂ * S⁻¹ = W₁ * W₂ ∧ S * X₃ * S⁻¹ = X₃⁻¹ ∧
      T * W₁ * T⁻¹ = W₁⁻¹ ∧ T * W₂ * T⁻¹ = W₂⁻¹ ∧ T * X₃ * T⁻¹ = X₃ ∧
      Function.Injective fun v : Fin 3 × Fin 3 × Fin 3 =>
        W₁ ^ (v.1 : ℕ) * W₂ ^ (v.2.1 : ℕ) * X₃ ^ (v.2.2 : ℕ) := by
  intro W₁ W₂ X₃ S T h1 h2 h3 h4 h5
  have e2 : W₂ = tau 2 * tau 0 * (tau 2)⁻¹ := by
    rw [h2, J3E27.wordW2, wordProd_append', wordProd_append', wordProd_invW', tau0, tau2]
  rw [← tau0] at h1
  rw [← tau1] at h3
  rw [← tau2] at h4
  rw [← tau3] at h5
  subst h1 h3 h4 h5 e2
  have r1 := rels_one (sW1 ++ sW1 ++ sW1, []) (by simp [rels])
  have r2 := rels_one (sW2 ++ sW2 ++ sW2, []) (by simp [rels])
  have r3 := rels_one (sX3 ++ sX3 ++ sX3, []) (by simp [rels])
  have r4 := rels_one (sW1 ++ sW2 ++ sW1i ++ sW2i, []) (by simp [rels])
  have r5 := rels_one (sW1 ++ sX3 ++ sW1i ++ sX3i, []) (by simp [rels])
  have r6 := rels_one (sW2 ++ sX3 ++ sW2i ++ sX3i, []) (by simp [rels])
  have r7 := rels_one (sS ++ sW2 ++ sSi ++ sW2i ++ sW1i, []) (by simp [rels])
  have r8 := rels_one (sS ++ sX3 ++ sSi ++ sX3, []) (by simp [rels])
  have r9 := rels_one (sT ++ sW1 ++ sTi ++ sW1, []) (by simp [rels])
  have r10 := rels_one (sT ++ sW2 ++ sTi ++ sW2, []) (by simp [rels])
  have r11 := rels_one (sT ++ sX3 ++ sTi ++ sX3i, []) (by simp [rels])
  simp only [sW1, sW1i, sW2, sW2i, sX3, sX3i, sS, sSi, sT, sTi, List.cons_append,
    List.nil_append, signedProd_cons, signedProd_nil, mul_one, ↓reduceIte,
    Bool.false_eq_true] at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_three]
    simpa only [mul_assoc] using r1
  · rw [pow_three]
    simpa only [mul_assoc] using r2
  · rw [pow_three]
    simpa only [mul_assoc] using r3
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r4
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r5
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r6
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r7
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r8
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r9
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r10
  · rw [← mul_inv_eq_one]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using r11
  intro v w hvw
  have hv : ∀ u : Fin 3 × Fin 3 × Fin 3,
      tau 0 ^ (u.1 : ℕ) * (tau 2 * tau 0 * (tau 2)⁻¹) ^ (u.2.1 : ℕ) * tau 1 ^ (u.2.2 : ℕ) =
        signedProd tau (prodW (9 * u.1 + 3 * u.2.1 + u.2.2)) := by
    intro u
    have q1 : (9 * (u.1 : ℕ) + 3 * u.2.1 + u.2.2) / 9 = u.1 := by omega
    have q2 : (9 * (u.1 : ℕ) + 3 * u.2.1 + u.2.2) / 3 % 3 = u.2.1 := by omega
    have q3 : (9 * (u.1 : ℕ) + 3 * u.2.1 + u.2.2) % 3 = u.2.2 := by omega
    rw [prodW, q1, q2, q3, signedProd_append, signedProd_append, signedProd_rep, signedProd_rep,
      signedProd_rep]
    simp only [sW1, sW2, sX3, signedProd_cons, signedProd_nil, mul_one, ↓reduceIte,
      Bool.false_eq_true, mul_assoc]
  have hvw' := hvw
  simp only at hvw'
  rw [hv v, hv w] at hvw'
  by_contra hne
  refine prods_ne (by omega) (by omega) ?_ hvw'
  intro e
  apply hne
  obtain ⟨v1, v2, v3⟩ := v
  obtain ⟨w1, w2, w3⟩ := w
  simp only at e
  simp only [Prod.mk.injEq, Fin.ext_iff]
  omega

end CertificateChecks.KernelJ3E27

end
