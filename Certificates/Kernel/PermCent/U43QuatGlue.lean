module

public import Certificates.Kernel.PermCent.U43QuatBind
public import Certificates.Kernel.PermCent.U43QuatBindA
public import Certificates.Kernel.PermCent.U43QuatBindB
public import Certificates.Kernel.PermCent.U43QuatMat
public import Certificates.Kernel.PermCent.U43QuatMatC
public import Certificates.Kernel.PermCent.U43QuatRt
public import Certificates.Kernel.PermCent.U43QuatId
public import Certificates.Kernel.PermCent.U43P1Rep
public import CFSG.Certificates.Kernel.QuatPackSound
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckD
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Check

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.QuatK CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.E4C CertificateChecks.KernelPermCent.U43P1 Subgroup
open CFSG.EvenSporadicStandard.M24Std.CU43 (P P_eq_range)

@[expose] noncomputable def qE (j : ℕ) : Equiv.Perm (Fin 820) := gK quatEls j

theorem quatEls_spec : ∀ j < 14, (quatEls.getD j (0, false)).2 = false ∧
    ((quatEls.getD j (0, false)), quatElDets.getD j 0) ∈ quatEls.zip quatElDets ∧
    uncode (quatElDets.getD j 0) ≠ 0 := by
  decide +kernel

theorem qspec {j : ℕ} (hj : j < 14) : (matK (quatEls.getD j (0, false)).1).det ≠ 0 ∧
    IsUnitaryF (glK (quatEls.getD j (0, false)).1) ∧
    (glK (quatEls.getD j (0, false)).1 : Matrix (Fin 4) (Fin 4) F9).det =
      uncode (quatElDets.getD j 0) := by
  obtain ⟨-, hm, hne⟩ := quatEls_spec j hj
  obtain ⟨hu, hd⟩ := quatEls_mat.2 _ hm
  have h0 : (matK (quatEls.getD j (0, false)).1).det ≠ 0 := by
    rw [hd]
    exact hne
  exact ⟨h0, isUnitaryF_glK h0 hu, by rw [glK_val h0, hd]⟩

theorem prep_qE {j : ℕ} (hj : j < 14) : PRep 820 10 (QP j) (qE j) := by
  have hm : matOK (quatEls.getD j (0, false)).1 (quatEls.getD j (0, false)).2 (QP j) = true := by
    rcases Nat.lt_or_ge j 7 with h | h
    · have hA := bindsQA
      rw [List.all_eq_true] at hA
      exact hA j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    · have hB := bindsQB
      rw [List.all_eq_true] at hB
      exact hB j (List.mem_range'_1.2 ⟨h, by omega⟩)
  exact prep_matOK (qspec hj).1 hm

theorem qE_eq {j : ℕ} (hj : j < 14) : qE j = perm820 (glK (quatEls.getD j (0, false)).1) := by
  simp only [qE, gK, eK, (quatEls_spec j hj).1, Bool.toNat_false, pow_zero, mul_one]

theorem qE_mem_range {j : ℕ} (hj : j < 14) (h5 : j ≠ 5) : qE j ∈ psi.range := by
  have hd : quatElDets.getD j 0 = 3 := by
    interval_cases j <;> first | rfl | omega
  obtain ⟨-, hu, hdet⟩ := qspec hj
  rw [qE_eq hj]
  exact perm820_mem_range hu (by rw [hdet, hd, uncode_three])

theorem qE_mem {j : ℕ} (hj : j < 14) (h5 : j ≠ 5) : qE j ∈ P := by
  rw [P_eq_range]
  exact qE_mem_range hj h5

theorem binds_facts :
    canonK 820 10 (mask 10) (820 * 10) (QP 14) = true ∧
      matOK repIn.1 repIn.2 rF = true ∧ isId (pc (QP 6) (QP 14)) = true ∧
      Nat.beq (mulK 820 10 w0F w0F) eP = true ∧
      Nat.beq (mulK 820 10 w0F rF) (mulK 820 10 rF w0F) = true ∧
      Nat.beq (mulK 820 10 u1F u1F) rF = true := by
  obtain ⟨h, -, -⟩ := bindsQ
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcan, -⟩, -⟩, hrIn⟩, hid⟩, -⟩, hww⟩, hwr⟩, hl1⟩, -⟩ := h
  rw [List.all_eq_true] at hcan hl1
  exact ⟨hcan 14 (List.mem_range.2 (by norm_num)), hrIn, hid, hww, hwr,
    hl1 u1F (by simp [l1F, q8K])⟩

theorem prep_c0inv : PRep 820 10 (QP 14) (qE 6)⁻¹ := by
  obtain ⟨hc, -, hid, -⟩ := binds_facts
  intro x
  have hlt := (CFSG.KS.PF.canon_facts hc).2.2.2 x x.2
  rw [isId, List.all_eq_true] at hid
  have h1 := Nat.eq_of_beq_eq_true (hid x (List.mem_range.2 x.2))
  rw [at10, pc, CFSG.KS.PF.pg_pcomp (by norm_num) x.2] at h1
  have h2 := prep_qE (j := 6) (by norm_num) ⟨_, hlt⟩
  have e : qE 6 ⟨_, hlt⟩ = x := Fin.ext (h2.symm.trans h1)
  have e' : (qE 6)⁻¹ x = ⟨_, hlt⟩ := (Equiv.Perm.inv_eq_iff_eq).2 e.symm
  rw [e']

@[expose] noncomputable def phi : Equiv.Perm (Fin 820) ≃* Equiv.Perm (Fin 820) :=
  MulAut.conj (qE 6)⁻¹

theorem phi_apply (X : Equiv.Perm (Fin 820)) : phi X = (qE 6)⁻¹ * (X * qE 6) := by
  simp [phi, MulAut.conj_apply, mul_assoc]

theorem crep_fr {x : ℕ} {X : Equiv.Perm (Fin 820)} (hx : PRep 820 10 x X) :
    CRep 820 10 (fr x) (phi X) := by
  rw [phi_apply]
  exact crep_mulK (by norm_num) (by norm_num) prep_c0inv (prep_pc hx (prep_qE (by norm_num)))

theorem prep_rIn : PRep 820 10 rF (tRep 0) :=
  prep_matOK (detOf_spec (detOf_rep 0 (by norm_num))).1 binds_facts.2.1

theorem conj_r0 : phi (qE 0) = tRep 0 := prep_eq (crep_fr (prep_qE (by norm_num))).1 prep_rIn

theorem crep_rF : CRep 820 10 rF (tRep 0) := by
  rw [← conj_r0]
  exact crep_fr (prep_qE (by norm_num))

theorem crep_eP : CRep 820 10 eP 1 := crep_pidn (by norm_num) (by norm_num)

@[expose] noncomputable def ofPk (p : ℕ) : Equiv.Perm (Fin 820) :=
  Classical.epsilon fun g => PRep 820 10 p g

theorem prep_ofPk {p : ℕ} {g : Equiv.Perm (Fin 820)} (h : PRep 820 10 p g) :
    PRep 820 10 p (ofPk p) :=
  Classical.epsilon_spec ⟨g, h⟩

theorem ofPk_eq {p : ℕ} {g : Equiv.Perm (Fin 820)} (h : PRep 820 10 p g) : ofPk p = g :=
  prep_eq (prep_ofPk h) h

theorem cen0_facts :
    (∀ y ∈ psi.range ⊓ centralizer ({tRep 0} : Set (Equiv.Perm (Fin 820))),
      ∃ i < 1152, PRep 820 10 (CgIn.T i) y) ∧
      ∀ i < 1152, PRep 820 10 (CgIn.T i) (ofPk (CgIn.T i)) := by
  obtain ⟨g1, g2, -, -, -, -, -, z1, z2, -, -, -, -, -, n1, n2, -, -, -, -, -, e1, e2, -⟩ :=
    bindsS_cen
  have hs := small
  rw [Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨hcm, hnm⟩ := hs
  obtain ⟨hCeq, -, -, -, -, -, ptsC⟩ := pair_facts (c := 0) (lC := cgIn) (lK := gsIn)
    (by norm_num) g1 g2 (by decide) (by decide) (by rw [e1]; rfl) (by rw [e2]; rfl) e1 e2
    CgIn.cl CgIn.tr (by decide) z1 baseL_lt CgIn.k KIn.cl KIn.tr (by decide) z2 baseL_lt KIn.k
    CgIn.h (fun j hj => by
      have h := hcm j (List.mem_range.2 hj)
      rw [Bool.and_eq_true] at h
      exact h) hnm (by rw [card_cen0, n1]) (by rw [n1]; norm_num) (by rw [n2]; norm_num)
  have hd : ∀ x ∈ cgIn, detOf x.1 ≠ 0 := by decide
  obtain ⟨-, hall, -⟩ := enum_group g1 hd (by rw [e1]; rfl) CgIn.cl CgIn.tr (by decide)
    (by rw [n1]; norm_num) z1 baseL_lt CgIn.k
  rw [e1, hCeq, n1] at hall
  refine ⟨hall, fun i hi => ?_⟩
  obtain ⟨y, -, hy⟩ := ptsC i (by rw [n1]; exact hi)
  exact prep_ofPk hy

@[expose] noncomputable def L0E : List (Equiv.Perm (Fin 820)) := q8Elems (qE 0) (qE 1) (qE 2)

@[expose] noncomputable def L1E : List (Equiv.Perm (Fin 820)) := q8Elems (qE 0) (qE 3) (qE 4)

theorem q8Elems_map (f : Equiv.Perm (Fin 820) ≃* Equiv.Perm (Fin 820))
    (r i j : Equiv.Perm (Fin 820)) : q8Elems (f r) (f i) (f j) = (q8Elems r i j).map f := by
  simp [q8Elems, map_mul, map_one]

theorem forall₂_q8F {a b : ℕ} (ha : a < 14) (hb : b < 14) :
    List.Forall₂ (CRep 820 10) (q8K 820 10 eP rF (fr (QP a)) (fr (QP b)))
      (q8Elems (tRep 0) (phi (qE a)) (phi (qE b))) :=
  q8K_forall₂ (by norm_num) (by norm_num) crep_eP crep_rF (crep_fr (prep_qE ha))
    (crep_fr (prep_qE hb))

theorem phi_mem {X : Equiv.Perm (Fin 820)} (hX : X ∈ P) :
    phi X ∈ P := by
  rw [phi_apply]
  have hc := qE_mem (j := 6) (by norm_num) (by norm_num)
  exact P.mul_mem (P.inv_mem hc) (P.mul_mem hX hc)

theorem ident_frame {K : Subgroup (Equiv.Perm (Fin 820))}
    (hd : CFSG.ClassicalInvolution.Q3.TL4.Vtx.AmbientQuatDatum P K (qE 0)) :
    ∃ L ∈ [L0E, L1E], ∀ x, x ∈ K ↔ x ∈ L := by
  obtain ⟨hcen, hpts⟩ := cen0_facts
  have hc0 : (qE 6)⁻¹ ∈ P := P.inv_mem (qE_mem (by norm_num) (by norm_num))
  have hd' := hd.conj hc0
  have e0 : (qE 6)⁻¹ * qE 0 * (qE 6)⁻¹⁻¹ = tRep 0 := conj_r0
  rw [e0] at hd'
  obtain ⟨hsq, hcan⟩ := Bool.and_eq_true _ _ ▸ roots_scan
  rw [List.all_eq_true] at hcan
  have hspec := sqScanK_spec (by norm_num) (by norm_num) hsq hpts crep_rF
  have hS : List.Forall₂ (CRep 820 10) (rootIdx.map CgIn.T)
      (rootIdx.map fun i => ofPk (CgIn.T i)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i hi => crep_of_canonK (hcan i hi) (hpts i (hspec.1 i hi))
  obtain ⟨-, -, -, hww, hwr, -⟩ := binds_facts
  have hw0 : CRep 820 10 w0F (phi (qE 7)) := crep_fr (prep_qE (by norm_num))
  have hww' : phi (qE 7) * phi (qE 7) = 1 := by
    have h := hww
    rw [beq_eq (by norm_num) (crep_mulK (by norm_num) (by norm_num) hw0.1 hw0.1) crep_eP,
      decide_eq_true_iff] at h
    exact h
  have hwinv : (phi (qE 7))⁻¹ = phi (qE 7) := inv_eq_of_mul_eq_one_right hww'
  have hW : List.Forall₂ (fun c C => CRep 820 10 c.1 C ∧ CRep 820 10 c.2 C⁻¹) [(w0F, w0F)]
      [phi (qE 7)] := .cons ⟨hw0, hwinv ▸ hw0⟩ .nil
  have hLs : List.Forall₂ (List.Forall₂ (CRep 820 10)) [l0F, l1F]
      [q8Elems (tRep 0) (phi (qE 1)) (phi (qE 2)), q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4))] :=
    .cons (forall₂_q8F (by norm_num) (by norm_num))
      (.cons (forall₂_q8F (by norm_num) (by norm_num)) .nil)
  have hc := ident_scan
  rw [identSqCheckK_eq (by norm_num) (by norm_num) crep_eP crep_rF hS hW hLs] at hc
  obtain ⟨L, hL, hKL⟩ := eq_of_identSqCheck hd' hc (fun u hu huu => by
      have hu' : u ∈ psi.range ⊓ centralizer ({tRep 0} : Set (Equiv.Perm (Fin 820))) := by
        refine mem_inf.2 ⟨P_eq_range ▸ hu, mem_centralizer_singleton_iff.2 ?_⟩
        rw [← huu, mul_assoc]
      obtain ⟨i, hi, hp⟩ := hcen u hu'
      have hiu := ofPk_eq hp
      have hmem := (hspec.2 i hi).1 (by rw [hiu, huu])
      exact List.mem_map.2 ⟨i, hmem, hiu⟩)
    (fun c hc => by
      rw [List.mem_singleton] at hc
      subst hc
      refine ⟨phi_mem (qE_mem (by norm_num) (by norm_num)), ?_⟩
      have h := hwr
      rw [beq_eq (by norm_num) (crep_mulK (by norm_num) (by norm_num) hw0.1 crep_rF.1)
        (crep_mulK (by norm_num) (by norm_num) crep_rF.1 hw0.1), decide_eq_true_iff] at h
      exact h)
  have hK : ∀ x, x ∈ K ↔ phi x ∈ conjSub (qE 6)⁻¹ K := fun x => by
    rw [mem_conjSub_iff, phi_apply]
    have e : (qE 6)⁻¹⁻¹ * ((qE 6)⁻¹ * (x * qE 6)) * (qE 6)⁻¹ = x := by group
    rw [e]
  rw [← conj_r0] at hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl
  · refine ⟨L0E, by simp, fun x => ?_⟩
    rw [hK, hKL, q8Elems_map, L0E, List.mem_map_of_injective phi.injective]
  · refine ⟨L1E, by simp, fun x => ?_⟩
    rw [hK, hKL, q8Elems_map, L1E, List.mem_map_of_injective phi.injective]

@[expose] noncomputable def K0E : Subgroup (Equiv.Perm (Fin 820)) := closure {qE 1, qE 2}

@[expose] noncomputable def K1E : Subgroup (Equiv.Perm (Fin 820)) := closure {qE 3, qE 4}

theorem glK_mul {a b c : ℕ} (ha : (matK a).det ≠ 0) (hb : (matK b).det ≠ 0)
    (hc : (matK c).det ≠ 0) (h : matK a * matK b = matK c) : glK a * glK b = glK c :=
  Units.ext (by rw [Units.val_mul, glK_val ha, glK_val hb, glK_val hc, h])

theorem u0_sq : qE 1 * qE 1 = qE 0 := by
  rw [qE_eq (by norm_num), qE_eq (by norm_num), ← map_mul,
    glK_mul (qspec (j := 1) (by norm_num)).1 (qspec (j := 1) (by norm_num)).1
      (qspec (j := 0) (by norm_num)).1 quat_mat_c2.2.2.2.2]

theorem u1_sq : qE 3 * qE 3 = qE 0 := by
  have h := binds_facts.2.2.2.2.2
  have hu1 : CRep 820 10 u1F (phi (qE 3)) := crep_fr (prep_qE (by norm_num))
  rw [beq_eq (by norm_num) (crep_mulK (by norm_num) (by norm_num) hu1.1 hu1.1) crep_rF,
    decide_eq_true_iff, ← conj_r0, ← map_mul] at h
  exact phi.injective h

theorem eq_closure_of_iff {K : Subgroup (Equiv.Perm (Fin 820))} {r i j : Equiv.Perm (Fin 820)}
    (hr : i * i = r) (hK : ∀ x, x ∈ K ↔ x ∈ q8Elems r i j) : K = closure {i, j} := by
  refine le_antisymm (fun x hx => q8Elems_sub hr x ((hK x).1 hx)) ?_
  rw [closure_le]
  rintro x (rfl | rfl)
  · exact (hK x).2 (by simp [q8Elems])
  · exact (hK x).2 (by simp [q8Elems])

theorem ident {K : Subgroup (Equiv.Perm (Fin 820))}
    (hd : CFSG.ClassicalInvolution.Q3.TL4.Vtx.AmbientQuatDatum P K (qE 0)) :
    K = K0E ∨ K = K1E := by
  obtain ⟨L, hL, hKL⟩ := ident_frame hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl
  · exact Or.inl (eq_closure_of_iff u0_sq hKL)
  · exact Or.inr (eq_closure_of_iff u1_sq hKL)

theorem card_inf_cen_conj {H : Subgroup (Equiv.Perm (Fin 820))} {g x : Equiv.Perm (Fin 820)}
    (hg : g ∈ H) : Nat.card ↥(H ⊓ centralizer ({g * x * g⁻¹} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(H ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) := by
  have e : (H ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))).map (MulAut.conj g).toMonoidHom =
      H ⊓ centralizer ({g * x * g⁻¹} : Set (Equiv.Perm (Fin 820))) := by
    ext y
    rw [mem_map_equiv, MulAut.conj_symm_apply, mem_inf, mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hy := H.mul_mem (H.mul_mem hg h1) (H.inv_mem hg)
      have ey : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [ey] at hy
      refine ⟨hy, ?_⟩
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h2]
        _ = g * x * g⁻¹ * y := by group
    · rintro ⟨h1, h2⟩
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg, ?_⟩
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h2]
        _ = x * (g⁻¹ * y * g) := by group
  rw [← e, card_map_of_injective (MulAut.conj g).injective]

theorem det_c2 : (matK cC2).det ≠ 0 := by
  rw [quat_mat_c2.2.1]
  decide

theorem det_c2inv : (matK cC2inv).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det quat_mat_c2.2.2.1
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem d2_conj : perm820 (glK cC2) ∈ psi.range ∧
    qE 5 = perm820 (glK cC2) * tRep 2 * (perm820 (glK cC2))⁻¹ := by
  obtain ⟨hu, hd, hinv, hconj, -⟩ := quat_mat_c2
  have hrep : (matK repM1b.1).det ≠ 0 := (detOf_spec (detOf_rep 2 (by norm_num))).1
  have hM1 : (matK cM1).det ≠ 0 := (qspec (j := 5) (by norm_num)).1
  have hI : glK cC2 * glK cC2inv = 1 :=
    Units.ext (by rw [Units.val_mul, glK_val det_c2, glK_val det_c2inv, hinv, Units.val_one])
  have hc : glK cC2 * glK repM1b.1 * glK cC2inv = glK cM1 :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, glK_val det_c2, glK_val hrep,
      glK_val det_c2inv, glK_val hM1, hconj])
  refine ⟨perm820_mem_range (isUnitaryF_glK det_c2 hu) (by rw [glK_val det_c2, hd, uncode_three]), ?_⟩
  have einv : (perm820 (glK cC2))⁻¹ = perm820 (glK cC2inv) := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right hI]
  have e2 : tRep 2 = perm820 (glK repM1b.1) := by
    simp only [tRep, eK, Bool.toNat_false, pow_zero, mul_one]
    rfl
  rw [einv, e2, ← map_mul, ← map_mul, hc, qE_eq (by norm_num)]
  rfl

theorem card_cen_d2 :
    Nat.card ↥(P ⊓ centralizer ({qE 5} : Set (Equiv.Perm (Fin 820)))) = 6048 := by
  obtain ⟨hc, he⟩ := d2_conj
  rw [P_eq_range, he, card_inf_cen_conj hc, card_cen2]

end CertificateChecks.KernelPermCent.U43Quat

end
