module

public import Certificates.Kernel.PermCent.U43QuatRelG
public import Certificates.Kernel.PermCent.U43QuatCfg
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1U0
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1U0

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.LieType.Multipliers.U43
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M CertificateChecks.KernelPermCent.U43P1 Subgroup
  CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.QuatK
open CFSG.EvenSporadicStandard.M24Std.CU43 (P P_eq_range tP)

theorem mem_closure_q8 {n : ℕ} {r i j : Equiv.Perm (Fin n)} (hi : i * i = r) (hj : j * j = r)
    (hr : r * r = 1) (hiji : i * j * i = j) (x : Equiv.Perm (Fin n)) :
    x ∈ closure ({i, j} : Set (Equiv.Perm (Fin n))) ↔ x ∈ q8Elems r i j := by
  refine ⟨fun hx => ?_, q8Elems_sub hi x⟩
  have ii : ∀ z, i * (i * z) = r * z := fun z => by rw [← mul_assoc, hi]
  have jj : ∀ z, j * (j * z) = r * z := fun z => by rw [← mul_assoc, hj]
  have rr : ∀ z, r * (r * z) = z := fun z => by rw [← mul_assoc, hr, one_mul]
  have ri : ∀ z, r * (i * z) = i * (r * z) := fun z => by
    rw [← hi]
    simp only [mul_assoc]
  have rj : ∀ z, r * (j * z) = j * (r * z) := fun z => by
    rw [← hj]
    simp only [mul_assoc]
  have ji : ∀ z, j * (i * z) = i * (j * (r * z)) := fun z => by
    rw [← hi]
    calc j * (i * z) = i * j * i * (i * z) := by rw [hiji]
      _ = i * (j * (i * i * z)) := by simp only [mul_assoc]
  have ri' : r * i = i * r := by simpa using ri 1
  have rj' : r * j = j * r := by simpa using rj 1
  have ji' : j * i = i * (j * r) := by simpa using ji 1
  have iinv : i⁻¹ = i * r := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hi, hr])
  have jinv : j⁻¹ = j * r := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hj, hr])
  induction hx using Subgroup.closure_induction_left with
  | one => simp [q8Elems]
  | mul_left a ha y _ hy =>
    simp only [q8Elems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases ha with rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [q8Elems, List.mem_cons, List.not_mem_nil, or_false, mul_assoc, mul_one, one_mul,
        ii, jj, rr, ri, rj, ji, hi, hj, hr, ri', rj', ji', true_or, or_true]
  | inv_mul_cancel a ha y _ hy =>
    simp only [q8Elems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases ha with rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [iinv, jinv, q8Elems, List.mem_cons, List.not_mem_nil, or_false, mul_assoc,
        mul_one, one_mul, ii, jj, rr, ri, rj, ji, hi, hj, hr, ri', rj', ji', true_or, or_true]

theorem conjSub_pair {G : Type*} [Group G] (g a b : G) :
    conjSub g (closure ({a, b} : Set G)) = closure {g * a * g⁻¹, g * b * g⁻¹} := by
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem conjSub_eq_of_mem {n : ℕ} {g a b : Equiv.Perm (Fin n)}
    (ha : g * a * g⁻¹ ∈ closure ({a, b} : Set (Equiv.Perm (Fin n))))
    (hb : g * b * g⁻¹ ∈ closure ({a, b} : Set (Equiv.Perm (Fin n)))) :
    conjSub g (closure ({a, b} : Set (Equiv.Perm (Fin n)))) = closure {a, b} := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [CFSG.ClassicalInvolution.Q3.TL4.Vtx.natCard_conjSub])
  rw [conjSub_pair, closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

theorem conj_eq {G : Type*} [Group G] {g a b : G} (h : g * a = b * g) : g * a * g⁻¹ = b :=
  mul_inv_eq_of_eq_mul h

theorem rel_gam_v0 :
    qE 8 * qE 2 = qE 2 * qE 0 * qE 8 ∧ qE 9 * qE 2 = qE 2 * qE 9 ∧
      qE 10 * qE 2 = qE 1 * qE 2 * qE 0 * qE 10 ∧ qE 11 * qE 2 = qE 1 * qE 2 * qE 11 ∧
      qE 12 * qE 2 = qE 2 * qE 12 ∧ qE 13 * qE 2 = qE 2 * qE 0 * qE 13 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3, h4, h5, h6⟩ :=
    quat_rels
  have v0 := val_q (j := 0) (by norm_num)
  have v1 := val_q (j := 1) (by norm_num)
  have v2 := val_q (j := 2) (by norm_num)
  have v8 := val_q (j := 8) (by norm_num)
  have v9 := val_q (j := 9) (by norm_num)
  have v10 := val_q (j := 10) (by norm_num)
  have v11 := val_q (j := 11) (by norm_num)
  have v12 := val_q (j := 12) (by norm_num)
  have v13 := val_q (j := 13) (by norm_num)
  have e0 := qE_eq' (j := 0) (by norm_num)
  have e1 := qE_eq' (j := 1) (by norm_num)
  have e2 := qE_eq' (j := 2) (by norm_num)
  have e8 := qE_eq' (j := 8) (by norm_num)
  have e9 := qE_eq' (j := 9) (by norm_num)
  have e10 := qE_eq' (j := 10) (by norm_num)
  have e11 := qE_eq' (j := 11) (by norm_num)
  have e12 := qE_eq' (j := 12) (by norm_num)
  have e13 := qE_eq' (j := 13) (by norm_num)
  simp only [e0, e1, e2, e8, e9, e10, e11, e12, e13, ← map_mul]
  refine ⟨pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_, pe_of_mat ?_⟩
  all_goals simp only [Units.val_mul, v0, v1, v2, v8, v9, v10, v11, v12, v13]
  exacts [h1, h2, h3, h4, h5, h6]

theorem perm_eq_qE {A : GL (Fin 4) F9} {j : ℕ} (hj : j < 14)
    (hA : (A : Matrix (Fin 4) (Fin 4) F9) = matK (qc j)) : perm820 A = qE j := by
  rw [qE_eq hj]
  exact congrArg perm820 (Units.ext (hA.trans (glK_val (qspec hj).1).symm))

theorem glN9_eq {k k' : ℕ} (hk : k = k') (h : (matK k').det ≠ 0) : glN9 k = glK k' := by
  subst hk
  exact Units.ext ((glN9_val h).trans (glK_val h).symm)

theorem r0_eq : r0P = qE 0 := perm_eq_qE (by norm_num) rfl

theorem u0_eq : u0P = qE 1 := perm_eq_qE (by norm_num) rfl

theorem v0_eq : v0P = qE 2 := perm_eq_qE (by norm_num) rfl

theorem u1_eq : u1P = qE 3 := perm_eq_qE (by norm_num) rfl

theorem v1_eq : v1P = qE 4 := perm_eq_qE (by norm_num) rfl

theorem d2_eq : d2P = qE 5 := perm_eq_qE (by norm_num) rfl

theorem w0_eq : w0P = qE 7 := by
  rw [w0P, qE_eq (by norm_num)]
  exact congrArg perm820 (glN9_eq rfl (qspec (j := 7) (by norm_num)).1)

theorem s01_eq : s01P = s01E := congrArg perm820 (glN9_eq rfl det_s01)

theorem y0_eq : y0P = y0E := congrArg perm820 (glN9_eq rfl det_y0)

theorem gamCodes_eq : gamCodes = (List.range 6).map fun j => qc (8 + j) := by
  decide +kernel

theorem gamP_eq : gamP = (List.range 6).map fun j => qE (8 + j) := by
  rw [gamP, gamCodes_eq, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj6 := List.mem_range.1 hj
  simp only [Function.comp_apply]
  rw [qE_eq (by omega)]
  exact congrArg perm820 (glN9_eq rfl (qspec (j := 8 + j) (by omega)).1)

theorem mem_gamP {c : Equiv.Perm (Fin 820)} : c ∈ gamP ↔ ∃ j < 6, c = qE (8 + j) := by
  rw [gamP_eq, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, List.mem_range.1 hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, List.mem_range.2 hj, rfl⟩

theorem K0_eq : K0 = K0E := by rw [K0, K0E, u0_eq, v0_eq]

theorem K1_eq : K1 = K1E := by rw [K1, K1E, u1_eq, v1_eq]

theorem L0_eq : L0P = L0E := by rw [L0P, L0E, r0_eq, u0_eq, v0_eq]

theorem L1_eq : L1P = L1E := by rw [L1P, L1E, r0_eq, u1_eq, v1_eq]

theorem v1_sq : qE 4 * qE 4 = qE 0 := by
  obtain ⟨h, -, -⟩ := bindsQ
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hl1⟩, -⟩ := h
  rw [List.all_eq_true] at hl1
  have h1 : Nat.beq (mulK 820 10 v1F v1F) rF = true := hl1 v1F (by simp [l1F, q8K])
  have hv1 : CRep 820 10 v1F (phi (qE 4)) := crep_fr (prep_qE (by norm_num))
  rw [beq_eq (by norm_num) (crep_mulK (by norm_num) (by norm_num) hv1.1 hv1.1) crep_rF,
    decide_eq_true_iff, ← conj_r0, ← map_mul] at h1
  exact phi.injective h1

theorem mem_K0E {x : Equiv.Perm (Fin 820)} (hx : x ∈ L0E) : x ∈ K0E :=
  q8Elems_sub u0_sq x hx

theorem conjSub_K0E {g a b : Equiv.Perm (Fin 820)} (ha : g * qE 1 = a * g) (hb : g * qE 2 = b * g)
    (ha' : a ∈ L0E) (hb' : b ∈ L0E) : conjSub g K0E = K0E :=
  conjSub_eq_of_mem (by rw [conj_eq ha]; exact mem_K0E ha') (by rw [conj_eq hb]; exact mem_K0E hb')

open Certificates in
open CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M CFSG.ClassicalInvolution.Generic in
open CFSG.EvenSporadicStandard.M24Std.CU43 (P) in
theorem facts55121 : (r0P ∈ P ∧ u0P ∈ P ∧ v0P ∈ P ∧ u1P ∈ P ∧ v1P ∈ P ∧ s01P ∈ P ∧ w0P ∈ P ∧ y0P ∈ P ∧
      ∀ c ∈ gamP, c ∈ P) ∧
    (r0P ≠ 1 ∧ r0P * r0P = 1 ∧ u0P * u0P = r0P ∧ (∀ x, x ∈ K0 ↔ x ∈ L0P) ∧
      u1P * u1P = r0P ∧ (∀ x, x ∈ K1 ↔ x ∈ L1P) ∧ d2P * u0P = u0P * d2P ∧
      d2P * v0P = v0P * d2P ∧ d2P * v1P ≠ v1P * d2P ∧ s01P * s01P = 1 ∧
      s01P * r0P = r0P * s01P ∧ conjSub s01P K1 = K0 ∧ conjSub s01P K0 = K1 ∧
      w0P * r0P = r0P * w0P ∧ (∀ c ∈ gamP, conjSub c K0 = K0) ∧
      y0P * (y0P * y0P) = 1 ∧ y0P * d2P = d2P * y0P ∧ conjSub y0P K0 = K0 ∧
      y0P * u0P ≠ u0P * y0P) ∧
    ∀ K : Subgroup (Equiv.Perm (Fin 820)),
      CFSG.ClassicalInvolution.Q3.TL4.Vtx.AmbientQuatDatum P K r0P → K = K0 ∨ K = K1 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ := rel_perm
  obtain ⟨n1, n2, n3⟩ := rel_ne
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := rel_gam_v0
  have hK0 : ∀ x, x ∈ K0E ↔ x ∈ L0E := mem_closure_q8 u0_sq p2 p1 p3
  have hK1 : ∀ x, x ∈ K1E ↔ x ∈ L1E := mem_closure_q8 u1_sq v1_sq p1 p4
  refine ⟨?_, ?_, fun K hd => ?_⟩
  · rw [r0_eq, u0_eq, v0_eq, u1_eq, v1_eq, s01_eq, w0_eq, y0_eq]
    refine ⟨qE_mem (by norm_num) (by norm_num), qE_mem (by norm_num) (by norm_num),
      qE_mem (by norm_num) (by norm_num), qE_mem (by norm_num) (by norm_num),
      qE_mem (by norm_num) (by norm_num), P_eq_range ▸ s01E_mem,
      qE_mem (by norm_num) (by norm_num), P_eq_range ▸ y0E_mem, fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := mem_gamP.1 hc
    exact qE_mem (by omega) (by omega)
  · rw [K0_eq, K1_eq, L0_eq, L1_eq, r0_eq, u0_eq, v0_eq, u1_eq, v1_eq, d2_eq, s01_eq, w0_eq,
      y0_eq]
    refine ⟨n1, p1, u0_sq, hK0, u1_sq, hK1, p5, p6, n2, p7, p12, ?_, ?_, p13, fun c hc => ?_,
      p14, p15, ?_, n3⟩
    · rw [K1E, conjSub_pair, conj_eq p8, conj_eq p9]
      rfl
    · rw [K0E, conjSub_pair, conj_eq p10, conj_eq p11]
      rfl
    · obtain ⟨j, hj, rfl⟩ := mem_gamP.1 hc
      have hu := rel_gam j hj
      interval_cases j
      · exact conjSub_K0E hu g1 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
      · exact conjSub_K0E hu g2 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
      · exact conjSub_K0E hu g3 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
      · exact conjSub_K0E hu g4 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
      · exact conjSub_K0E hu g5 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
      · exact conjSub_K0E hu g6 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
    · exact conjSub_K0E p16 p17 (by simp [L0E, q8Elems]) (by simp [L0E, q8Elems])
  · rw [r0_eq] at hd
    rw [K0_eq, K1_eq]
    exact ident hd

open Certificates in
open CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M in
open CFSG.EvenSporadicStandard.M24Std.CU43 (P tP) in
theorem facts55122 : (∀ g ∈ P, ∀ k < 8, CfgCore (g * tP k) → ∃ c ∈ gamP, g * tP k = c * d2P * c⁻¹) ∧
    Nat.card ↥(P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820)))) = 6048 := by
  refine ⟨fun g hg k hk hcfg => ?_, ?_⟩
  · have hE : CfgE (g * tP k) := by
      have h := hcfg
      rw [CfgCore, L1_eq, u0_eq, v0_eq, u1_eq, v1_eq] at h
      exact h
    obtain ⟨j, hj, e⟩ := cfg_classify hg hk hE
    exact ⟨qE (8 + j), mem_gamP.2 ⟨j, hj, rfl⟩, by rw [d2_eq]; exact e⟩
  · rw [d2_eq]
    exact card_cen_d2

end CertificateChecks.KernelPermCent.U43Quat

end
