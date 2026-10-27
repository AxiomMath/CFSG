
module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.HN.F5Group
public import Certificates.Kernel.Ly3085.FiberCount
public import Certificates.Kernel.Ly3085.FiberGlue

@[expose] public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open CertificateChecks.KernelSporSch
open Matrix MulAction

theorem restrArr_lt (X : Mat) {t : ℕ} (ht : t < 49) : (restrArr X)[t]! < 5 := by
  unfold restrArr
  simp only
  rw [CFSG.KS.SporSch.LyM.ofFn_get! _ ht]
  unfold mulXU
  rw [CFSG.KS.SporSch.LyM.ofFn_get! _ (by omega), CFSG.KS.SporSch.LyM.ofFn_get! _ (by omega)]
  exact Nat.mod_lt _ (by norm_num)

theorem ofArr_eq (ra : Array ℕ) : CFSG.KD.LyOm.ofArr ra =
    CFSG.KS.LyOm.Pack.packR (fun t => ra[t]!) (fun t => 11 * t) 49 := rfl

theorem smM_ofArr {ra : Array ℕ} (hra : ∀ t < 49, ra[t]! < 5) :
    smM (CFSG.KD.LyOm.ofArr ra) = mat7 ra := by
  ext i j
  simp only [smM, ent, mat7, Matrix.of_apply]
  have e : 77 * i.val + 11 * j.val = 11 * (7 * i.val + j.val) := by ring
  rw [e, ofArr_eq, CFSG.KS.LyOm.Pack.packR_lane (π := fun t => t)
    (fun t ht => lt_trans (hra t ht) (by norm_num)) (fun _ _ _ _ e => e) (by omega)]

theorem ra_facts [LySeed] {j : ℕ}
    (hj : j < 5) : smM (CFSG.KD.LyOm.ofArr (LySv.RA[j]!)) = restr7 (aStar (j + 2)) := by
  rw [← genArr_eq j hj, smM_ofArr (ra := genArr j) (fun t ht => by
    unfold genArr
    exact restrArr_lt _ ht), mat7_genArr]

theorem fixed_of_conj {R B : Matrix (Fin 7) (Fin 7) (ZMod 5)} (hR : IsUnit R.det)
    (h : Rᵀ * B * R = B) : (R⁻¹)ᵀ * B * R⁻¹ = B := by
  calc (R⁻¹)ᵀ * B * R⁻¹ = (R⁻¹)ᵀ * (Rᵀ * B * R) * R⁻¹ := by rw [h]
    _ = (R * R⁻¹)ᵀ * B * (R * R⁻¹) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = B := by rw [Matrix.mul_nonsing_inv _ hR, Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one]

theorem beta2_fixed
    [LySeed] (h : lyH) : h • fm CFSG.KD.LyOm.BE2 = fm CFSG.KD.LyOm.BE2 := by
  have hb := recAnd (p := fun j => (fun R => bAnd(CFSG.KC.LyOm.sVld CFSG.KD.LyOm.SC R,
    Nat.beq (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC (CFSG.KC.LyOm.sTr R)
      (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC CFSG.KD.LyOm.BE2 R)) CFSG.KD.LyOm.BE2))
      (CFSG.KD.LyOm.ofArr (LySv.RA[j]!))) 5 CFSG.KD.LyOm.beta2
  obtain ⟨-, -, -, cBE, -⟩ := rep2
  have hgen : ∀ j < 5, (⟨aStar (j + 2), aStar_mem_lyH (by omega)⟩ : lyH) ∈
      stabilizer lyH (fm CFSG.KD.LyOm.BE2) := by
    intro j hj
    obtain ⟨h1, h2⟩ := bAnd_true (hb j hj)
    have cR := sVld_sound hSC h1
    have eR := ra_facts hj
    obtain ⟨cT, eT⟩ := CFSG.KS.LyOm.Pack.sTr_sound cR
    have m1 := smul7 cBE cR
    have m2 := smul7 cT m1.1
    have e := beq_eq h2
    have hconj : (restr7 (aStar (j + 2)))ᵀ * smM CFSG.KD.LyOm.BE2 * restr7 (aStar (j + 2)) =
        smM CFSG.KD.LyOm.BE2 := by
      rw [← eR, ← eT, Matrix.mul_assoc, ← m1.2, ← m2.2, e]
    have hu : IsUnit (restr7 (aStar (j + 2))).det := by
      have e1 : restr7 (aStar (j + 2)) * restr7 (aStar (j + 2))⁻¹ = 1 :=
        restr7_mul_inv (lyH_le_stabU (aStar_mem_lyH (by omega)))
      exact Matrix.isUnit_det_of_right_inverse e1
    rw [mem_stabilizer_iff]
    ext1
    rw [form7_smul_M, restr7_inv', fm_smM]
    exact fixed_of_conj hu hconj
  let T : Subgroup J := (stabilizer lyH (fm CFSG.KD.LyOm.BE2)).map lyH.subtype
  have hle : lyH ≤ T := by
    rw [lyH, Subgroup.closure_le]
    rintro _ ⟨j, ⟨h2, h6⟩, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    exact ⟨_, hgen k (by omega), rfl⟩
  obtain ⟨x, hx, hxe⟩ := hle h.2
  have : x = h := Subtype.ext hxe
  rw [← this]
  exact hx

theorem form_zero
    [LySeed] (h : lyH) : h • (⟨0⟩ : Form7) = ⟨0⟩ := by
  ext1
  rw [form7_smul_M, Matrix.mul_zero, Matrix.zero_mul]

theorem form_unit
    [LySeed] (h : lyH) (X : Form7) :
    IsUnit (h • X).M.det ↔ IsUnit X.M.det := by
  rw [form7_smul_M, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hu : IsUnit (restr7 ((h⁻¹ : lyH) : J)).det := by
    have e1 : restr7 ((h⁻¹ : lyH) : J) * restr7 (((h⁻¹)⁻¹ : lyH) : J) = 1 := by
      rw [← restr7_mulH, mul_inv_cancel, Subgroup.coe_one, restr7_one]
    exact Matrix.isUnit_det_of_right_inverse e1
  constructor
  · intro hx
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hx)
  · intro hx
    exact (hu.mul hx).mul hu

theorem smM_zero : smM 0 = 0 := by
  ext i j
  simp [smM, ent]

theorem canon_zero : LCanon 11 7 7 0 := ⟨by positivity, fun i _ j _ => by simp⟩

theorem beta_facts
    [LySeed] :
    fm CFSG.KD.LyOm.BE1 = ⟨0⟩ ∧ IsUnit (fm CFSG.KD.LyOm.BE2).M.det ∧
      fm CFSG.KD.LyOm.BE3 ≠ ⟨0⟩ ∧ ¬ IsUnit (fm CFSG.KD.LyOm.BE3).M.det ∧
      IsUnit (fm CFSG.KD.LyOm.BE4).M.det ∧ fm CFSG.KD.LyOm.BE2 ≠ fm CFSG.KD.LyOm.BE4 := by
  obtain ⟨b1, b24, cI2, eI2, cI4, eI4, b3, cX, x0, xb⟩ := beta_parts
  obtain ⟨-, -, -, c2, -⟩ := rep2
  obtain ⟨-, -, -, c3, -⟩ := rep3
  obtain ⟨-, -, -, c4, -⟩ := rep4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext1
    rw [fm_smM, b1, smM_zero]
  · rw [fm_smM]
    rw [(smul7 c2 cI2).2] at eI2
    exact Matrix.isUnit_det_of_right_inverse eI2
  · intro e
    apply b3
    apply smM_inj c3 canon_zero
    rw [smM_zero, ← fm_smM, e]
  · intro hu
    have e := (smul7 cX c3).2
    rw [xb, smM_zero] at e
    rw [fm_smM] at hu
    have : smM CFSG.KD.LyOm.X3 = 0 := by
      calc smM CFSG.KD.LyOm.X3 = smM CFSG.KD.LyOm.X3 * smM CFSG.KD.LyOm.BE3 *
            (smM CFSG.KD.LyOm.BE3)⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
        _ = 0 := by rw [← e, Matrix.zero_mul]
    exact x0 (smM_inj cX canon_zero (by rw [this, smM_zero]))
  · rw [fm_smM]
    rw [(smul7 c4 cI4).2] at eI4
    exact Matrix.isUnit_det_of_right_inverse eI4
  · intro e
    apply b24
    apply smM_inj c2 c4
    rw [← fm_smM, ← fm_smM, e]

theorem disjoint_orbits [LySeed] {a b : LyOperator}
    (h : ∀ g : lyH, g • a ≠ b) :
    Disjoint (Set.toFinite (orbit lyH a)).toFinset (Set.toFinite (orbit lyH b)).toFinset := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [Set.Finite.mem_toFinset] at hxa hxb
  obtain ⟨g, rfl⟩ := hxa
  obtain ⟨g', hg'⟩ := hxb
  change g' • b = g • a at hg'
  apply h (g'⁻¹ * g)
  rw [mul_smul, ← hg', inv_smul_smul]

theorem orbit_opE
    [LySeed] (g : lyH) : g • opE = opE := by
  rw [Subgroup.smul_def]
  exact lyH_le_stab g.2

theorem sep_of_beta
    [LySeed] {a b : LyOperator} (h : ∀ g : lyH, g • beta a ≠ beta b) :
    ∀ g : lyH, g • a ≠ b := by
  intro g e
  apply h g
  rw [← beta_smulH, e]

theorem card_lyH_ge
    [LySeed] : 5859000000 ≤ Nat.card lyH := by
  let ψ : lyH' →* lyK := (rhoP.comp lyH'.subtype).codRestrict lyK (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hH' : Nat.card lyH' = Nat.card lyH :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyH_le_stabU).toEquiv
  have := Nat.card_le_card_of_surjective ψ hψ
  have hK := card_image_ge
  omega

theorem beta_rep1
    [LySeed] : beta (gRep 1 • opE) = fm CFSG.KD.LyOm.BE1 := by
  ext1
  rw [fm_smM, rep1.2.2.2.2]

theorem beta_rep2
    [LySeed] : beta (gRep 2 • opE) = fm CFSG.KD.LyOm.BE2 := by
  ext1
  rw [fm_smM, rep2.2.2.2.2]

@[expose] def repOp [LySeed] (c : ℕ) : LyOperator :=
  if c = 0 then opE else gRep c • opE

@[expose] def subO [LySeed] (i : Fin 5) : Finset LyOperator :=
  (Set.toFinite (orbit lyH (repOp i.val))).toFinset

theorem card_subO [LySeed] (i : Fin 5) :
    (subO i).card = Nat.card (orbit lyH (repOp i.val)) := by
  unfold subO
  rw [← Set.ncard_eq_toFinset_card]
  exact (Nat.card_coe_set_eq _).symm

theorem repOp_zero [LySeed] : repOp 0 = opE := if_pos rfl

theorem repOp_pos [LySeed] {c : ℕ} (hc : c ≠ 0) : repOp c = gRep c • opE :=
  if_neg hc

theorem orbit_opE_eq
    [LySeed] : orbit lyH opE = {opE} := by
  ext x
  constructor
  · rintro ⟨g', rfl⟩
    exact orbit_opE g'
  · rintro rfl
    exact mem_orbit_self _

end CertificateChecks.KernelLy.Omega

end
