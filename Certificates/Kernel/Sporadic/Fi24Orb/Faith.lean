
module

public import Certificates.Kernel.Sporadic.Fi24Orb.Simple
import Certificates.Kernel.Sporadic.Fi24Orb.Small

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24Fix TauCeti TauCeti.Sporadic CFSG.Sporadic.Bridge
  CFSG.KC.Fi24FixC CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KC.Fi24OrbT CFSG.KD.Fi24Orb
  CFSG.KS.Mat3

noncomputable abbrev M0 : Subgroup Jc := MulAction.stabilizer Jc (0 : Fin N)

theorem card_M0 : Nat.card M0 = 4089470473293004800 := by
  have h := Subgroup.card_mul_index M0
  have hN : Nat.card (Fin N) = N := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [MulAction.index_stabilizer_of_transitive, hN, card_Jc] at h
  have h2 : Nat.card M0 * N = 4089470473293004800 * N := by
    rw [h]
    norm_num [N]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num [N]) h2

theorem mem_M0 {g : Jc} : g ∈ M0 ↔ act g root = root := by
  rw [MulAction.mem_stabilizer_iff, smul_iff]
  change act g (f 0) = f 0 ↔ _
  rw [f_zero]

noncomputable abbrev Mg : Subgroup (GL (Fin 781) (ZMod 3)) := M0.map Jc.subtype

theorem card_Mg : Nat.card Mg = 4089470473293004800 := by
  rw [Subgroup.card_map_of_injective Jc.subtype_injective, card_M0]

theorem SG_le_Mg : SG ≤ Mg := by
  intro g hg
  refine ⟨⟨g, SG_le uA_Jc uB_Jc hg⟩, mem_M0.2 (SG_fix hg), rfl⟩

theorem SG_eq_Mg : SG = Mg :=
  Subgroup.eq_of_le_of_card_ge SG_le_Mg (by rw [card_Mg]; exact card_SG)

theorem card_Sst_eq : Nat.card Sst = 4089470473293004800 := by
  have h := SG_eq ▸ SG_eq_Mg ▸ card_Mg
  rw [Subgroup.card_map_of_injective (stab (colSp Mb)).subtype_injective] at h
  exact h

theorem card_conj : Nat.card (CFSG.Sporadic.Fi23.J.map (MulAut.conj Pu⁻¹).toMonoidHom) =
    4089470473293004800 := by
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj Pu⁻¹).toMonoidHom)
    (MulAut.conj Pu⁻¹).injective, CFSG.Sporadic.Fi23.card_J]

theorem Sρ_eq : Sρ = CFSG.Sporadic.Fi23.J.map (MulAut.conj Pu⁻¹).toMonoidHom := by
  refine (Subgroup.eq_of_le_of_card_ge conj_le ?_).symm
  rw [card_conj, ← card_Sst_eq, ← map_Sst]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd Sst ρ)

noncomputable abbrev ρS : Sst →* GL (Fin 253) (ZMod 3) := ρ.comp Sst.subtype

theorem ρS_range : ρS.range = Sρ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, map_Sst]

theorem ρS_bij : Function.Bijective ρS.rangeRestrict := by
  rw [Nat.bijective_iff_surjective_and_card]
  refine ⟨ρS.rangeRestrict_surjective, ?_⟩
  rw [ρS_range, card_Sst_eq, Sρ_eq, card_conj]

instance : IsSimpleGroup CFSG.Sporadic.Fi23.J := CFSG.Sporadic.Fi23.isSimpleGroup_J

theorem isSimple_Sst : IsSimpleGroup Sst := by
  let e1 : Sst ≃* ρS.range := MulEquiv.ofBijective ρS.rangeRestrict ρS_bij
  let e2 : ρS.range ≃* CFSG.Sporadic.Fi23.J.map (MulAut.conj Pu⁻¹).toMonoidHom :=
    MulEquiv.subgroupCongr (ρS_range.trans Sρ_eq)
  let e3 : CFSG.Sporadic.Fi23.J ≃* CFSG.Sporadic.Fi23.J.map (MulAut.conj Pu⁻¹).toMonoidHom :=
    CFSG.Sporadic.Fi23.J.equivMapOfInjective _ (MulAut.conj Pu⁻¹).injective
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_J
    (e1.trans (e2.trans e3.symm))

theorem isSimple_M0 : IsSimpleGroup M0 := by
  let e1 : M0 ≃* Mg := M0.equivMapOfInjective _ Jc.subtype_injective
  let e2 : Mg ≃* SG := MulEquiv.subgroupCongr SG_eq_Mg.symm
  let e3 : SG ≃* Sst.map (stab (colSp Mb)).subtype := MulEquiv.subgroupCongr SG_eq
  let e4 : Sst ≃* Sst.map (stab (colSp Mb)).subtype :=
    Sst.equivMapOfInjective _ (stab (colSp Mb)).subtype_injective
  exact @MulEquiv.isSimpleGroup _ _ _ _ isSimple_Sst (e1.trans (e2.trans (e3.trans e4.symm)))

noncomputable def Ker : Subgroup Jc where
  carrier := {h | ∀ i : Fin N, h • i = i}
  one_mem' := fun i => one_smul _ i
  mul_mem' := fun {a b} ha hb i => by
    simp only [Set.mem_setOf_eq] at *
    rw [mul_smul, hb, ha]
  inv_mem' := fun {a} ha i => by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha i]
    exact inv_smul_smul a i

theorem mem_Ker {h : Jc} : h ∈ Ker ↔ ∀ i : Fin N, h • i = i := Iff.rfl

instance Ker_normal : Ker.Normal where
  conj_mem n hn c := by
    rw [mem_Ker] at hn ⊢
    intro i
    rw [mul_smul, mul_smul, hn, smul_inv_smul]

theorem Ker_le : Ker ≤ M0 := fun h hh => (mem_Ker.1 hh) 0

theorem x5_not_Ker : xJ 5 ∉ Ker := by
  intro h
  have hi := (mem_Ker.1 (Ker.inv_mem h)) (pr (r := 1) (by norm_num))
  rw [xJ_smul_pr (by norm_num) (by norm_num)] at hi
  have := pr_inj _ _ hi
  rw [Nat.eq_of_beq_eq_true t5] at this
  exact absurd this (by norm_num)

theorem Ker_eq_bot : Ker = ⊥ := by
  have := isSimple_M0
  have : (Ker.subgroupOf M0).Normal := Subgroup.Normal.subgroupOf Ker_normal M0
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ker.subgroupOf M0) with h | h
  · rw [eq_bot_iff]
    intro g hg
    have hm : (⟨g, Ker_le hg⟩ : M0) ∈ Ker.subgroupOf M0 := hg
    rw [h, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hm
  · exfalso
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Jc (0 : Fin N) p0
    have hy : c⁻¹ * xJ 5 * c ∈ M0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hc, xJ_fix (h0_stab (by norm_num)
        (by norm_num)), ← hc, inv_smul_smul]
    have hK : c⁻¹ * xJ 5 * c ∈ Ker := by
      have : (⟨_, hy⟩ : M0) ∈ Ker.subgroupOf M0 := by rw [h]; trivial
      exact this
    apply x5_not_Ker
    have := Ker_normal.conj_mem _ hK c
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel,
      mul_one] at this

instance faithful : FaithfulSMul Jc (Fin N) where
  eq_of_smul_eq_smul {g h} H := by
    have hk : h⁻¹ * g ∈ Ker := fun i => by rw [mul_smul, H, inv_smul_smul]
    rw [Ker_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hk
    exact hk.symm

theorem c23 : Canon3 609961 (CFSG.KD.BrFi24.RB 23) := canon_RB (by norm_num) (by norm_num)

theorem c24 : Canon3 609961 (CFSG.KD.BrFi24.RB 24) := canon_RB (by norm_num) (by norm_num)

theorem mat_ONE : mat3 781 609961 CFSG.KD.BrFi24.ONE = 1 :=
  CertificateChecks.KernelSpor.Fi24Rels.hs.one_mt

theorem ne_one_of {X : ℕ} (hX : Canon3 609961 X) (h : CFSG.KC.Ord.notB (Nat.beq X CFSG.KD.BrFi24.ONE) = true)
    : mat3 781 609961 X ≠ 1 := by
  intro e
  rw [← mat_ONE] at e
  have := mat3_inj (d := 781) (by norm_num) hX CertificateChecks.KernelSpor.Fi24Rels.hs.one_q e
  rw [this, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem pow_29 (M : Matrix (Fin 781) (Fin 781) (ZMod 3)) :
    (M * M * (M * M)) * (M * M * (M * M)) * ((M * M * (M * M)) * (M * M * (M * M))) *
      ((M * M * (M * M)) * (M * M * (M * M)) * ((M * M * (M * M)) * M)) = M ^ 29 := by
  simp only [← pow_two, ← pow_succ, ← pow_add, ← pow_mul]
  norm_num [← pow_add, ← pow_mul, pow_two]

theorem pow29_mat {X : ℕ} (hX : Canon3 609961 X) :
    mat3 781 609961 (pow29 CFSG.KD.BrFi24.MUL X) = mat3 781 609961 X ^ 29 := by
  have hs := CertificateChecks.KernelSpor.Fi24Rels.hs
  obtain ⟨c2, e2⟩ := hs.mul_sound _ _ hX hX
  obtain ⟨c4, e4⟩ := hs.mul_sound _ _ c2 c2
  obtain ⟨c8, e8⟩ := hs.mul_sound _ _ c4 c4
  obtain ⟨c16, e16⟩ := hs.mul_sound _ _ c8 c8
  obtain ⟨c5, e5⟩ := hs.mul_sound _ _ c4 hX
  obtain ⟨c13, e13⟩ := hs.mul_sound _ _ c8 c5
  obtain ⟨-, e29⟩ := hs.mul_sound _ _ c16 c13
  unfold pow29
  simp only [strictN_eq3]
  rw [e29, e16, e13, e8, e5, e4, e2]
  exact pow_29 _

noncomputable def aJ : Jc := ⟨uA, uA_Jc⟩

noncomputable def bJ : Jc := ⟨uB, uB_Jc⟩

theorem uA_mat : (uA : Matrix (Fin 781) (Fin 781) (ZMod 3)) = mat3 781 609961 (CFSG.KD.BrFi24.RB 23) :=
  mat_RB23.symm

theorem uB_mat : (uB : Matrix (Fin 781) (Fin 781) (ZMod 3)) = mat3 781 609961 (CFSG.KD.BrFi24.RB 24) :=
  mat_RB24.symm

theorem aJ_sq : aJ ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h := Nat.eq_of_beq_eq_true a_sq
  obtain ⟨-, e⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c23 c23
  rw [h, mat_ONE] at e
  change ((uA ^ 2 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = 1
  rw [pow_two, Units.val_mul, uA_mat, ← e]

theorem aJ_ne : aJ ≠ 1 := by
  intro h
  have := congrArg (fun g : Jc => ((g : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3))) h
  change (uA : Matrix (Fin 781) (Fin 781) (ZMod 3)) = 1 at this
  rw [uA_mat] at this
  exact ne_one_of c23 a_ne this

theorem bJ_cube : bJ ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h := Nat.eq_of_beq_eq_true b_cube
  obtain ⟨c2, e2⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c24 c24
  obtain ⟨-, e3⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c24 c2
  rw [h, mat_ONE, e2] at e3
  change ((uB ^ 3 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = 1
  rw [pow_three, Units.val_mul, Units.val_mul, uB_mat, ← e3]

theorem bJ_ne : bJ ≠ 1 := by
  intro h
  have := congrArg (fun g : Jc => ((g : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3))) h
  change (uB : Matrix (Fin 781) (Fin 781) (ZMod 3)) = 1 at this
  rw [uB_mat] at this
  exact ne_one_of c24 b_ne this

theorem abJ_mat : (((aJ * bJ : Jc) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    mat3 781 609961 (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 24)) := by
  obtain ⟨-, e⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c23 c24
  rw [e]
  change ((uA * uB : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = _
  rw [Units.val_mul, uA_mat, uB_mat]

theorem abJ_pow : (aJ * bJ) ^ 29 = 1 := by
  apply Subtype.ext
  apply Units.ext
  have c := (CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c23 c24).1
  have h := Nat.eq_of_beq_eq_true ab_pow
  have e := pow29_mat c
  rw [h, mat_ONE] at e
  change ((((aJ * bJ) ^ 29 : Jc) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = 1
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, abJ_mat, e]

theorem abJ_ne : aJ * bJ ≠ 1 := by
  intro h
  have : (((aJ * bJ : Jc) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = 1 := by
    rw [h]
    rfl
  rw [abJ_mat] at this
  exact ne_one_of (CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c23 c24).1 ab_ne this

theorem orderOf_aJ : orderOf aJ = 2 := orderOf_eq_prime aJ_sq aJ_ne

theorem orderOf_bJ : orderOf bJ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime bJ_cube bJ_ne

theorem orderOf_abJ : orderOf (aJ * bJ) = 29 := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact orderOf_eq_prime abJ_pow abJ_ne

theorem closure_aJ_bJ : Subgroup.closure ({aJ, bJ} : Set Jc) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    {g : GL (Fin 781) (ZMod 3) | g.val = CFSG.Sporadic.Fi24.mA ∨ g.val = CFSG.Sporadic.Fi24.mB}
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype,
    Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl uA_val
    · exact Or.inr uB_val
  · rintro (h | h)
    · left
      exact Subtype.ext (Units.ext (h.trans uA_val.symm))
    · right
      exact Subtype.ext (Units.ext (h.trans uB_val.symm))

theorem isSimpleGroup_Jc : IsSimpleGroup Jc := by
  refine CFSG.Sporadic.Th.isSimpleGroup_of_primitive_coprime_orders (Ω := Fin N) ?_ aJ bJ
    closure_aJ_bJ 0 ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  · rw [orderOf_aJ, orderOf_bJ]
    norm_num
  · rw [orderOf_abJ, card_M0]
    norm_num

end CertificateChecks.KernelFi24Orb

end
