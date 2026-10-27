
module

public import Certificates.Kernel.Sporadic.Fi24Orb.Inj
public import Certificates.Kernel.Sporadic.Fi24Orb.Restr
public import CFSG.Sporadic.Presentation.Fi24PrimeInputs
import Certificates.Kernel.Fi24.Bridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24Fix TauCeti TauCeti.Sporadic CFSG.Sporadic.Bridge
  CFSG.KC.Fi24FixC CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbT CFSG.KD.Fi24Orb

noncomputable scoped instance (priority := high) actGL :
    MulAction (GL (Fin 781) (ZMod 3)) (Submodule (ZMod 3) (Fin 781 → ZMod 3)) where
  smul g W := act g W
  one_smul W := act_one W
  mul_smul g h W := act_mul g h W

theorem smul_eq (g : GL (Fin 781) (ZMod 3)) (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    g • W = act g W := rfl

noncomputable abbrev root : Submodule (ZMod 3) (Fin 781 → ZMod 3) := (CFSG.Sporadic.Fi24.pt 0).sp

noncomputable abbrev Ω : Set (Submodule (ZMod 3) (Fin 781 → ZMod 3)) := {W | ∃ r < N, ψ r = W}

theorem ncard_Ω : Ω.ncard = N := by
  have e : Ω = ((Finset.range N).image ψ : Set _) := by
    ext W
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  rw [e, Set.ncard_coe_finset, Finset.card_image_of_injOn (fun r hr r' hr' h =>
    ψ_inj (Finset.mem_range.1 hr) (Finset.mem_range.1 hr') h), Finset.card_range]

theorem root_mem : root ∈ Ω := ⟨NM 0, NM_lt (by norm_num), ψ_root⟩

theorem orbit_Γ : MulAction.orbit Γ root = Ω := by
  obtain ⟨g0, hg0, e0⟩ := (mem_range_ψ root).1 ⟨NM 0, NM_lt (by norm_num), ψ_root⟩
  ext W
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine (mem_range_ψ _).2 ⟨g * g0, Γ.mul_mem hg hg0, ?_⟩
    change act (g * g0) V0 = act g root
    rw [act_mul, e0]
  · intro hW
    obtain ⟨h, hh, rfl⟩ := (mem_range_ψ W).1 hW
    refine ⟨⟨h * g0⁻¹, Γ.mul_mem hh (Γ.inv_mem hg0)⟩, ?_⟩
    change act (h * g0⁻¹) root = act h V0
    rw [act_mul, ← e0, act_inv_act]

theorem card_eq_mul {G : Subgroup (GL (Fin 781) (ZMod 3))} (h : MulAction.orbit G root = Ω) :
    Nat.card G = N * Nat.card (MulAction.stabilizer G root) := by
  rw [← Subgroup.card_mul_index (MulAction.stabilizer G root), MulAction.index_stabilizer, h,
    ncard_Ω, mul_comm]

noncomputable abbrev Jc : Subgroup (GL (Fin 781) (ZMod 3)) :=
  Subgroup.closure {g | g.val = CFSG.Sporadic.Fi24.mA ∨ g.val = CFSG.Sporadic.Fi24.mB}

theorem uA_Jc : uA ∈ Jc := Subgroup.subset_closure (Or.inl uA_val)

theorem uB_Jc : uB ∈ Jc := Subgroup.subset_closure (Or.inr uB_val)

theorem Jc_le : Jc ≤ Γ := by
  rw [Subgroup.closure_le]
  intro g hg
  exact seeds_mem g hg

theorem wU_mem {G : Subgroup (GL (Fin 781) (ZMod 3))} (hA : uA ∈ G) (hB : uB ∈ G) :
    ∀ w : List ℕ, wU w ∈ G
  | [] => G.one_mem
  | k :: w => by
    refine G.mul_mem ?_ (wU_mem hA hB w)
    split_ifs
    · exact hA
    · exact hB

noncomputable abbrev SG : Subgroup (GL (Fin 781) (ZMod 3)) := Subgroup.closure {W1u, W2u}

theorem SG_eq : SG = Sst.map (stab (colSp Mb)).subtype := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem card_SG : 4089470473293004800 ≤ Nat.card SG := by
  rw [SG_eq, Subgroup.card_map_of_injective (stab (colSp Mb)).subtype_injective]
  exact card_Sst

theorem SG_le_stab : SG ≤ stab (colSp Mb) := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact W1_stab
  · exact W2_stab

theorem SG_fix {g : GL (Fin 781) (ZMod 3)} (hg : g ∈ SG) : act g root = root := by
  have := mem_stab.1 (SG_le_stab hg)
  rwa [colSp_Mb] at this

theorem SG_le {G : Subgroup (GL (Fin 781) (ZMod 3))} (hA : uA ∈ G) (hB : uB ∈ G) : SG ≤ G := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact wU_mem hA hB W1
  · exact wU_mem hA hB W2

theorem card_stab_ge {G : Subgroup (GL (Fin 781) (ZMod 3))} (hA : uA ∈ G) (hB : uB ∈ G) :
    4089470473293004800 ≤ Nat.card (MulAction.stabilizer G root) := by
  refine le_trans card_SG ?_
  have hle : SG.subgroupOf G ≤ MulAction.stabilizer G root := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MulAction.mem_stabilizer_iff]
    exact SG_fix hg
  calc Nat.card SG = Nat.card (SG.subgroupOf G) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (SG_le hA hB)).toEquiv).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem card_Γ_le : Nat.card Γ ≤ 1255205709190661721292800 := by
  obtain ⟨hfin, hcard⟩ := CertificateChecks.KernelFi24.fi24Prime
  have e : SporadicName.Fi24Prime.presentation = fi24PrimePresentation := rfl
  have hfin' : Finite fi24PrimePresentation.Group := by
    rw [← e]
    exact hfin
  have hcard' : Nat.card fi24PrimePresentation.Group ≤ 1255205709190661721292800 := by
    rw [← e]
    exact hcard
  exact le_trans (Nat.card_le_card_of_surjective _ σ.rangeRestrict_surjective) hcard'

theorem card_Γ : Nat.card Γ = 1255205709190661721292800 := by
  refine le_antisymm card_Γ_le ?_
  rw [card_eq_mul orbit_Γ]
  have := card_stab_ge uA_mem uB_mem
  norm_num [N] at this ⊢
  omega

theorem orbit_Jc : MulAction.orbit Jc root = Ω := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    rw [← orbit_Γ]
    exact ⟨⟨g, Jc_le hg⟩, rfl⟩
  · rintro W ⟨r, hr, rfl⟩
    obtain ⟨k, hk, rfl⟩ := NM_surj hr
    change f k ∈ _
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [f_zero]
        exact MulAction.mem_orbit_self _
      · obtain ⟨hp, hl⟩ := tree hk (Nat.pos_iff_ne_zero.1 hpos)
        have hpN : oPar (OL k) < N := by omega
        obtain ⟨⟨g, hg⟩, e⟩ := ih _ hp hpN (NM_lt hpN)
        have e' : act g root = f (oPar (OL k)) := e
        rcases hl with ⟨-, he⟩ | ⟨-, he⟩
        · refine ⟨⟨uA * g, Jc.mul_mem uA_Jc hg⟩, ?_⟩
          change act (uA * g) root = f k
          rw [act_mul, e', ← f_α hpN, he]
        · refine ⟨⟨uB * g, Jc.mul_mem uB_Jc hg⟩, ?_⟩
          change act (uB * g) root = f k
          rw [act_mul, e', ← f_β hpN, he]

theorem card_Jc : Nat.card Jc = 1255205709190661721292800 := by
  refine le_antisymm (card_Γ ▸ Subgroup.card_le_of_le Jc_le) ?_
  rw [card_eq_mul orbit_Jc]
  have := card_stab_ge uA_Jc uB_Jc
  norm_num [N] at this ⊢
  omega

theorem Jc_eq : Jc = Γ := Subgroup.eq_of_le_of_card_ge Jc_le (by rw [card_Γ, card_Jc])

theorem card_stab_Jc : Nat.card (MulAction.stabilizer Jc root) = 4089470473293004800 := by
  have h := card_eq_mul orbit_Jc
  rw [card_Jc] at h
  change 1255205709190661721292800 = 306936 * Nat.card (MulAction.stabilizer Jc root) at h
  omega

end CertificateChecks.KernelFi24Orb

end
