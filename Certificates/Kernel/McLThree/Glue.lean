module

public import Certificates.Kernel.McLThree.Chk
public import Certificates.Kernel.McLNine.Glue
public import CFSG.Certificates.Kernel.McLThreeSound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage

public section

namespace CertificateChecks.KernelSpor.McLThree

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.KS.McLNine CFSG.KS.McLThree CertificateChecks.KernelSpor.McLNine CFSG.QuasithinUnique
  CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Lang.E6Descent CFSG.Open

open scoped Pointwise

set_option maxRecDepth 400000

theorem letters_p0 : ∀ w ∈ mclIndexThreeP0Words, Letters w := by
  simp only [Letters]
  decide

theorem letters_m0 : Letters (mclIndexThreeMoverWords.getD 0 []) := by
  simp only [Letters]
  decide

theorem letters_m1 : Letters (mclIndexThreeMoverWords.getD 1 []) := by
  simp only [Letters]
  decide

theorem letters_a : Letters mclIndexThreeA := by
  simp only [Letters]
  decide

theorem letters_g : Letters mclIndexThreeG := by
  simp only [Letters]
  decide

@[expose] noncomputable def ug (j : Nat) : Equiv.Perm (Fin 275) :=
  wP g9 (mclIndexNineUWords.getD j [])

theorem gen_O2 : ∀ j < 3, ug j q0 ∈ O2 ∧ ug j q1 ∈ O2 :=
  (mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g chk).1

theorem gen_mover : 1 < 3 ∧ ug 1 q0 = q1 :=
  (mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g chk).2.1

theorem orbit_wit : ∀ q : Fin 275, q ∉ O2 → (∀ j < 3, ug j q = q) ∨
    ∃ a < 4, ∃ b < 4, ∃ c < 4, q ≠ ug a q ∧ q ≠ ug b (ug c q) ∧ ug a q ≠ ug b (ug c q) :=
  (mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g chk).2.2.1

theorem p0w_fix : ∀ w ∈ mclIndexThreeP0Words, wP g9 w p0 = p0 :=
  (mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g
    chk).2.2.2.1

theorem p0w_pair : mclIndexThreeP0Words.Pairwise (fun w v =>
    ¬(wP g9 w q0 = wP g9 v q0 ∧ wP g9 w q1 = wP g9 v q1) ∧
      ¬(wP g9 w q0 = wP g9 v q1 ∧ wP g9 w q1 = wP g9 v q0)) :=
  (mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g
    chk).2.2.2.2.1

theorem mover_facts : (∀ s ∈ S3, wP g9 (mclIndexThreeMoverWords.getD 0 []) s ∈ S3) ∧
    (∀ s ∈ S3, wP g9 (mclIndexThreeMoverWords.getD 1 []) s ∈ S3) ∧
    wP g9 (mclIndexThreeMoverWords.getD 0 []) p0 = q0 ∧
    wP g9 (mclIndexThreeMoverWords.getD 1 []) p0 = q1 :=
  let h := mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g chk
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

theorem ag_facts : (∀ s ∈ S3, wP g9 mclIndexThreeA s ∈ S3) ∧ wP g9 mclIndexThreeA ^ 3 = 1 ∧
    wP g9 mclIndexThreeA ≠ 1 ∧
    wP g9 mclIndexThreeG * wP g9 mclIndexThreeA =
      wP g9 mclIndexThreeA * wP g9 mclIndexThreeA * wP g9 mclIndexThreeG :=
  (mcl3K_sound hF9 rfl letters_u letters_p0 letters_m0 letters_m1 letters_a letters_g
    chk).2.2.2.2.2.2.2.2.2

theorem ug_mem : ∀ j < 4, ug j ∈ U9gen := by
  intro j hj
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · exact subset_closure ⟨⟨j, h3⟩, rfl⟩
  · have e : j = 3 := by omega
    subst e
    have e1 : ug 3 = 1 := by
      unfold ug
      rw [List.getD_eq_default _ _ (by decide)]
      simp [wP]
    rw [e1]
    exact one_mem _

theorem q0_ne_q1 : q0 ≠ q1 := by decide

theorem smul_O2_of {x : Equiv.Perm (Fin 275)} (h0 : x q0 ∈ O2) (h1 : x q1 ∈ O2) :
    x • O2 = O2 := by
  have hne : x q0 ≠ x q1 := fun e => q0_ne_q1 (x.injective e)
  have himg : x • O2 = {x q0, x q1} := by
    rw [O2, Set.smul_set_insert, Set.smul_set_singleton]
    rfl
  rw [himg]
  simp only [O2, Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hne ⊢
  · exact absurd rfl hne
  · rfl
  · exact Set.pair_comm q1 q0
  · exact absurd rfl hne

theorem U9gen_le_stab_O2 :
    U9gen ≤ MulAction.stabilizer (Equiv.Perm (Fin 275)) O2 := by
  rw [U9gen, closure_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact smul_O2_of (gen_O2 j j.2).1 (gen_O2 j j.2).2

theorem orbit_q0 : MulAction.orbit U9gen q0 = O2 := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hu : (u : Equiv.Perm (Fin 275)) • O2 = O2 :=
      MulAction.mem_stabilizer_iff.mp (U9gen_le_stab_O2 u.2)
    have hq0 : q0 ∈ O2 := Set.mem_insert _ _
    have hm := Set.smul_mem_smul_set (a := (u : Equiv.Perm (Fin 275))) hq0
    rw [hu] at hm
    exact hm
  · intro hx
    simp only [O2, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact MulAction.mem_orbit_self _
    · exact MulAction.mem_orbit_iff.mpr ⟨⟨ug 1, ug_mem 1 (by norm_num)⟩, gen_mover.2⟩

theorem O2_card : Nat.card O2 = 2 := by
  rw [Nat.card_coe_set_eq, O2, Set.ncard_pair q0_ne_q1]

theorem orbit_eq_O2_of_card_two (q : Fin 275)
    (hq : Nat.card (MulAction.orbit U9gen q) = 2) : MulAction.orbit U9gen q = O2 := by
  by_cases hqO : q ∈ O2
  · have hqo : q ∈ MulAction.orbit U9gen q0 := by
      rw [orbit_q0]
      exact hqO
    rw [MulAction.orbit_eq_iff.mpr hqo, orbit_q0]
  · exfalso
    rcases orbit_wit q hqO with hfix | ⟨a, ha, b, hb, c, hc, n1, n2, n3⟩
    · have hle : U9gen ≤ MulAction.stabilizer (Equiv.Perm (Fin 275)) q := by
        rw [U9gen, closure_le]
        rintro _ ⟨j, rfl⟩
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
        exact hfix j j.2
      have hsub : MulAction.orbit U9gen q ⊆ {q} := by
        rintro _ ⟨u, rfl⟩
        exact Set.mem_singleton_iff.mpr (MulAction.mem_stabilizer_iff.mp (hle u.2))
      have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton q)
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, hq] at h1
      omega
    · have hsub : ({q, ug a q, ug b (ug c q)} : Set (Fin 275)) ⊆ MulAction.orbit U9gen q := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact MulAction.mem_orbit_self _
        · exact MulAction.mem_orbit_iff.mpr ⟨⟨ug a, ug_mem a ha⟩, rfl⟩
        · exact MulAction.mem_orbit_iff.mpr
            ⟨⟨ug b * ug c, U9gen.mul_mem (ug_mem b hb) (ug_mem c hc)⟩, rfl⟩
      have h3 : ({q, ug a q, ug b (ug c q)} : Set (Fin 275)).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨q, ug a q, ug b (ug c q), n1, n2, n3, rfl⟩
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [h3, ← Nat.card_coe_set_eq, hq] at h1
      omega

@[expose] noncomputable def P3 : Subgroup ↥mclP :=
  (MulAction.stabilizer mclCt S3).map (Subgroup.inclusion (inf_le_left : mclCt ≤ mclP))

theorem mem_P3_iff (g : ↥mclP) : g ∈ P3 ↔ g.val ∈ mclCt ∧ g.val • S3 = S3 := by
  rw [P3]
  constructor
  · intro hg
    obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp hg
    have hval : (h : Equiv.Perm (Fin 275)) = g.val := congrArg Subtype.val hhg
    rw [← hval]
    exact ⟨h.2, by simpa [Subgroup.smul_def] using hh⟩
  · rintro ⟨hct, hstab⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨g.val, hct⟩, by simpa [Subgroup.smul_def] using hstab, rfl⟩

theorem smul_S_of (x : Equiv.Perm (Fin 275)) (h0 : x p0 = p0) (hO2 : x • O2 = O2) :
    x • S3 = S3 := by
  change x '' (insert p0 O2) = insert p0 O2
  rw [Set.image_insert_eq, h0]
  have hO2' : x '' O2 = O2 := hO2
  rw [hO2']

theorem smul_orbit_self {u : Equiv.Perm (Fin 275)} (hu : u ∈ U9gen) (q : Fin 275) :
    u • MulAction.orbit U9gen q = MulAction.orbit U9gen q := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [MulAction.mem_orbit_iff] at hz ⊢
    obtain ⟨v, -, rfl⟩ := hz
    refine ⟨⟨u * (v : Equiv.Perm (Fin 275)), U9gen.mul_mem hu v.2⟩, ?_⟩
    simp [Subgroup.smul_def, mul_smul]
  · intro hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨v, -, rfl⟩ := hy
    rw [Set.mem_smul_set]
    refine ⟨(u⁻¹ * v) • q, MulAction.mem_orbit_iff.mpr
      ⟨⟨u⁻¹ * v, U9gen.mul_mem (U9gen.inv_mem hu) v.2⟩, rfl⟩, ?_⟩
    simp [Subgroup.smul_def, mul_smul]

theorem smul_orbit {x : Equiv.Perm (Fin 275)}
    (hx : x ∈ Subgroup.normalizer (U9gen : Set (Equiv.Perm (Fin 275)))) (q : Fin 275) :
    x • MulAction.orbit U9gen q = MulAction.orbit U9gen (x • q) := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [MulAction.mem_orbit_iff] at hz ⊢
    obtain ⟨v, -, rfl⟩ := hz
    refine ⟨⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx v).mp v.2⟩, ?_⟩
    simp [Subgroup.smul_def, mul_smul]
  · intro hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨v, -, rfl⟩ := hy
    rw [Set.mem_smul_set]
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (U9gen : Set (Equiv.Perm (Fin 275))) :=
      (Subgroup.normalizer _).inv_mem hx
    have hmem : x⁻¹ * (v : Equiv.Perm (Fin 275)) * x ∈ U9gen :=
      (Subgroup.mem_normalizer_iff.mp hxinv v).mp v.2
    refine ⟨(x⁻¹ * v * x) • q, MulAction.mem_orbit_iff.mpr ⟨⟨x⁻¹ * v * x, hmem⟩, rfl⟩, ?_⟩
    simp [Subgroup.smul_def, mul_smul]

theorem smul_S_of_maps {x : Equiv.Perm (Fin 275)} (h : ∀ s ∈ S3, x s ∈ S3) : x • S3 = S3 := by
  have hsub : x • S3 ⊆ S3 := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_smul_set]

theorem p0w_mem_P9
    {w : List Nat} (hw : w ∈ mclIndexThreeP0Words) :
    (⟨wP g9 w, (inf_le_left : mclCt ≤ mclP) (wP_mem_ct (letters_p0 w hw))⟩ : ↥mclP) ∈ P9 :=
  (mem_P9_iff _).mpr ⟨wP_mem_ct (letters_p0 w hw), p0w_fix w hw⟩

theorem smul_O2_eq (x : Equiv.Perm (Fin 275)) : x • O2 = {x q0, x q1} := by
  rw [O2, Set.smul_set_insert, Set.smul_set_singleton]
  rfl

theorem P0Orbit_ge_nine :
    9 ≤ Nat.card (MulAction.orbit P9 O2) := by
  let f : List Nat → Set (Fin 275) := fun w => wP g9 w • O2
  have hnodup : (mclIndexThreeP0Words.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine p0w_pair.imp fun {w v} hd heq => ?_
    have heq' : ({wP g9 w q0, wP g9 w q1} : Set (Fin 275)) = {wP g9 v q0, wP g9 v q1} := by
      rw [← smul_O2_eq, ← smul_O2_eq]
      exact heq
    rcases Set.pair_eq_pair_iff.mp heq' with h | h
    · exact hd.1 h
    · exact hd.2 h
  have hlen : (mclIndexThreeP0Words.map f).length = 9 := by simp [mclIndexThreeP0Words]
  have hsub : (↑((mclIndexThreeP0Words.map f).toFinset) : Set (Set (Fin 275))) ⊆
      MulAction.orbit P9 O2 := by
    intro X hX
    rw [Finset.mem_coe, List.mem_toFinset] at hX
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hX
    refine MulAction.mem_orbit_iff.mpr ⟨⟨_, p0w_mem_P9 hw⟩, ?_⟩
    simp [Subgroup.smul_def, f]
  calc 9 = ((mclIndexThreeP0Words.map f).toFinset).card := by
        rw [List.toFinset_card_of_nodup hnodup, hlen]
    _ = (((mclIndexThreeP0Words.map f).toFinset : Finset (Set (Fin 275))) : Set _).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (MulAction.orbit P9 O2).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (MulAction.orbit P9 O2) := (Nat.card_coe_set_eq _).symm

theorem P0Orbit_le_nine :
    Nat.card (MulAction.orbit P9 O2) ≤ 9 := by
  have hUle : U9.subgroupOf P9 ≤ MulAction.stabilizer P9 O2 := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    rw [MulAction.mem_stabilizer_iff]
    have hgen : (u.val : ↥mclP).val ∈ U9gen := hu
    have h := smul_orbit_self hgen q0
    rw [orbit_q0] at h
    simpa [Subgroup.smul_def] using h
  have h1 := (MulAction.stabilizer P9 O2).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have hP : Nat.card P9 = 1152 := by
    rw [P9_card, U9_card]
  rw [hP] at h1
  have hstab : 128 ≤ Nat.card (MulAction.stabilizer P9 O2) := by
    calc 128 = Nat.card U9 := U9_card.symm
      _ = Nat.card ↥(U9.subgroupOf P9) := by
          rw [card_subgroupOf_of_le U9_le_P9]
      _ ≤ Nat.card (MulAction.stabilizer P9 O2) := Subgroup.card_le_of_le hUle
  have hmul : 128 * Nat.card (MulAction.orbit P9 O2) ≤ 1152 := by
    calc 128 * _ ≤ Nat.card (MulAction.stabilizer P9 O2) * Nat.card (MulAction.orbit P9 O2) :=
          Nat.mul_le_mul_right _ hstab
      _ = 1152 := by rw [Nat.card_coe_set_eq]; exact h1
  omega

theorem P0Orbit_card :
    Nat.card (MulAction.orbit P9 O2) = 9 ∧ Nat.card (MulAction.stabilizer P9 O2) = 128 := by
  have horbit : Nat.card (MulAction.orbit P9 O2) = 9 := le_antisymm P0Orbit_le_nine P0Orbit_ge_nine
  have h1 := (MulAction.stabilizer P9 O2).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have hP : Nat.card P9 = 1152 := by
    rw [P9_card, U9_card]
  rw [hP] at h1
  have horbitN : (MulAction.orbit P9 O2).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact horbit
  rw [horbitN] at h1
  refine ⟨horbit, ?_⟩
  omega

theorem U9_le_P3 :
    U9 ≤ P3 := by
  intro u hu
  rw [mem_P3_iff]
  refine ⟨Subgroup.mem_subgroupOf.mp (P9_le_C (U9_le_P9 hu)), ?_⟩
  have hgen : u.val ∈ U9gen := hu
  have hfix : u.val p0 = p0 := U9_fix u hu
  have hO2 : u.val • O2 = O2 := by
    rw [← orbit_q0]
    exact smul_orbit_self hgen q0
  exact smul_S_of u.val hfix hO2

theorem p0_not_mem_O2 : p0 ∉ O2 := by
  simp only [O2, Set.mem_insert_iff, Set.mem_singleton_iff, p0, q0, q1, Fin.ext_iff]
  decide

theorem smul_O2_of_smul_S (x : Equiv.Perm (Fin 275)) (h0 : x p0 = p0) (hS : x • S3 = S3) :
    x • O2 = O2 := by
  have hS' : x '' (insert p0 O2) = insert p0 O2 := hS
  rw [Set.image_insert_eq, h0] at hS'
  have hp0xO2 : p0 ∉ x '' O2 := by
    rintro ⟨y, hy, hxy⟩
    have hy0 : y = p0 := x.injective (hxy.trans h0.symm)
    exact p0_not_mem_O2 (hy0 ▸ hy)
  change x '' O2 = O2
  ext y
  constructor
  · intro hy
    have hmem : y ∈ insert p0 (x '' O2) := Set.mem_insert_of_mem _ hy
    rw [hS'] at hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · rw [h] at hy
      exact absurd hy hp0xO2
    · exact h
  · intro hy
    have hmem : y ∈ insert p0 O2 := Set.mem_insert_of_mem _ hy
    rw [← hS'] at hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · rw [h] at hy
      exact absurd hy p0_not_mem_O2
    · exact h

theorem x_mem_normalizer
    (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9)
    {x : Equiv.Perm (Fin 275)}
    (hxconj : ∀ g : ↥mclP, ((α g : ↥mclP) : Equiv.Perm (Fin 275)) = x * g.val * x⁻¹) :
    x ∈ Subgroup.normalizer (U9gen : Set (Equiv.Perm (Fin 275))) := by
  have hαinv : U9.map (α.symm).toMonoidHom = U9 := by
    simpa using (Subgroup.map_symm_eq_iff_map_eq (H := U9) (K := U9) (e := α)).mpr hα
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have huP : (⟨u, U9gen_le_mclP hu⟩ : ↥mclP) ∈ U9 := hu
    have hαu : α ⟨u, U9gen_le_mclP hu⟩ ∈ U9 := by
      rw [← hα]
      exact Subgroup.mem_map_of_mem α.toMonoidHom huP
    have h := hxconj ⟨u, U9gen_le_mclP hu⟩
    rw [← h]
    exact Subgroup.mem_subgroupOf.mp hαu
  · intro hxu
    let w : ↥mclP := ⟨x * u * x⁻¹, U9gen_le_mclP hxu⟩
    have hwP : w ∈ U9 := hxu
    have hαw : (α.symm) w ∈ U9 := by
      rw [← hαinv]
      exact Subgroup.mem_map_of_mem (α.symm).toMonoidHom hwP
    have hgeneq : (((α.symm) w : ↥mclP) : Equiv.Perm (Fin 275)) = u := by
      have h := hxconj ((α.symm) w)
      have hαw' : α ((α.symm) w) = w := by simp
      rw [hαw'] at h
      have hx : x * (((α.symm) w : ↥mclP) : Equiv.Perm (Fin 275)) * x⁻¹ = x * u * x⁻¹ := by
        rw [← h]
      calc (((α.symm) w : ↥mclP) : Equiv.Perm (Fin 275))
          = x⁻¹ * (x * (((α.symm) w : ↥mclP) : Equiv.Perm (Fin 275)) * x⁻¹) * x := by group
        _ = x⁻¹ * (x * u * x⁻¹) * x := by rw [hx]
        _ = u := by group
    have hmem : (((α.symm) w : ↥mclP) : Equiv.Perm (Fin 275)) ∈ U9gen :=
      Subgroup.mem_subgroupOf.mp hαw
    rwa [hgeneq] at hmem

theorem x_smul_O2
    (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9)
    {x : Equiv.Perm (Fin 275)}
    (hxconj : ∀ g : ↥mclP, ((α g : ↥mclP) : Equiv.Perm (Fin 275)) = x * g.val * x⁻¹) :
    x • O2 = O2 := by
  have hxN := x_mem_normalizer α hα hxconj
  have hcard :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.card_orbit_apply_of_mem_normalizer
      hxN q0
  have h2 : Nat.card (MulAction.orbit U9gen (x q0)) = 2 := by
    rw [hcard, orbit_q0, O2_card]
  have hxorbit := orbit_eq_O2_of_card_two (x q0) h2
  calc x • O2 = x • MulAction.orbit U9gen q0 := by rw [orbit_q0]
    _ = MulAction.orbit U9gen (x • q0) := smul_orbit hxN _
    _ = O2 := by simpa [Equiv.Perm.smul_def] using hxorbit

theorem mover_mem_P3
    {w : List Nat} (hw : Letters w) (hS : ∀ s ∈ S3, wP g9 w s ∈ S3) :
    (⟨wP g9 w, (inf_le_left : mclCt ≤ mclP) (wP_mem_ct hw)⟩ : ↥mclP) ∈ P3 :=
  (mem_P3_iff _).mpr ⟨wP_mem_ct hw, smul_S_of_maps hS⟩

theorem P3_orbit_ge_three :
    3 ≤ Nat.card (MulAction.orbit P3 p0) := by
  obtain ⟨hs0, hs1, hi0, hi1⟩ := mover_facts
  have hq0 : q0 ∈ MulAction.orbit P3 p0 :=
    MulAction.mem_orbit_iff.mpr ⟨⟨_, mover_mem_P3 letters_m0 hs0⟩, hi0⟩
  have hq1 : q1 ∈ MulAction.orbit P3 p0 :=
    MulAction.mem_orbit_iff.mpr ⟨⟨_, mover_mem_P3 letters_m1 hs1⟩, hi1⟩
  have hsub : ({p0, q0, q1} : Set (Fin 275)) ⊆ MulAction.orbit P3 p0 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact MulAction.mem_orbit_self _
    · exact hq0
    · exact hq1
  have h3 : ({p0, q0, q1} : Set (Fin 275)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨p0, q0, q1, by decide, by decide, q0_ne_q1, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at h1
  exact h1

theorem P3_orbit_le_three :
    Nat.card (MulAction.orbit P3 p0) ≤ 3 := by
  have hp0S : p0 ∈ S3 := Set.mem_insert _ _
  have hsub : MulAction.orbit P3 p0 ⊆ S3 := by
    intro y hy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    have hgS : (g : ↥mclP).val • S3 = S3 := ((mem_P3_iff g).mp g.2).2
    have hmem : (g : ↥mclP).val • p0 ∈ (g : ↥mclP).val • S3 :=
      Set.smul_mem_smul_set hp0S
    rw [hgS] at hmem
    exact hmem
  have hScard : S3.ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨p0, q0, q1, by decide, by decide, q0_ne_q1, rfl⟩
  calc Nat.card (MulAction.orbit P3 p0) = (MulAction.orbit P3 p0).ncard := Nat.card_coe_set_eq _
    _ ≤ S3.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 3 := hScard

noncomputable def K3ToP0Stab
    (g : ↥(MulAction.stabilizer P3 p0)) :
    ↥(MulAction.stabilizer P9 O2) :=
  let gp : ↥mclP := g.1.1
  have hgP : gp ∈ P3 := g.1.2
  have hct : gp.val ∈ mclCt := ((mem_P3_iff gp).mp hgP).1
  have hS : gp.val • S3 = S3 := ((mem_P3_iff gp).mp hgP).2
  have hp0 : gp.val p0 = p0 := by
    have := (MulAction.mem_stabilizer_iff.mp g.2 : g.1 • p0 = p0)
    simpa [Subgroup.smul_def, gp] using this
  have hP0 : gp ∈ P9 := (mem_P9_iff gp).mpr ⟨hct, hp0⟩
  have hO2 : gp.val • O2 = O2 := smul_O2_of_smul_S gp.val hp0 hS
  ⟨⟨gp, hP0⟩, by simpa [Subgroup.smul_def] using hO2⟩

theorem K3_le :
    Nat.card (MulAction.stabilizer P3 p0) ≤ 128 := by
  have hinj : Function.Injective K3ToP0Stab := by
    intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(MulAction.stabilizer P9 O2) => (x.1.1 : ↥mclP)) heq
  have hle := Nat.card_le_card_of_injective K3ToP0Stab hinj
  rwa [P0Orbit_card.2] at hle

theorem K3_ge :
    128 ≤ Nat.card (MulAction.stabilizer P3 p0) := by
  have hUle : U9.subgroupOf P3 ≤ MulAction.stabilizer P3 p0 := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    rw [MulAction.mem_stabilizer_iff]
    have hfix : (u.val : ↥mclP).val p0 = p0 := U9_fix u.val hu
    simpa [Subgroup.smul_def] using hfix
  calc 128 = Nat.card U9 := U9_card.symm
    _ = Nat.card ↥(U9.subgroupOf P3) := by rw [card_subgroupOf_of_le U9_le_P3]
    _ ≤ Nat.card (MulAction.stabilizer P3 p0) := Subgroup.card_le_of_le hUle

theorem P3_card :
    Nat.card P3 = 3 * Nat.card U9 := by
  have hK : Nat.card (MulAction.stabilizer P3 p0) = 128 := le_antisymm K3_le K3_ge
  have h1 := (MulAction.stabilizer P3 p0).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have horbit : (MulAction.orbit P3 p0).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact le_antisymm P3_orbit_le_three P3_orbit_ge_three
  rw [hK, horbit] at h1
  rw [U9_card]
  omega

@[expose] noncomputable def AElem :
    ↥mclP :=
  ⟨wP g9 mclIndexThreeA, (inf_le_left : mclCt ≤ mclP) (wP_mem_ct letters_a)⟩

@[expose] noncomputable def GElem :
    ↥mclP :=
  ⟨wP g9 mclIndexThreeG, (inf_le_left : mclCt ≤ mclP) (wP_mem_ct letters_g)⟩

theorem AElem_mem_P3 :
    AElem ∈ P3 :=
  mover_mem_P3 letters_a ag_facts.1

theorem AElem_pow_three :
    AElem ^ 3 = 1 :=
  Subtype.ext ag_facts.2.1

theorem AElem_ne_one :
    AElem ≠ 1 :=
  fun h => ag_facts.2.2.1 (congrArg Subtype.val h)

theorem GElem_inv :
    GElem * AElem * GElem⁻¹ = AElem⁻¹ := by
  have hrel : GElem * AElem = AElem * AElem * GElem := Subtype.ext ag_facts.2.2.2
  have ha2 : AElem * AElem = AElem⁻¹ := by
    have h3 : AElem * AElem * AElem = 1 := by
      rw [← pow_two, ← pow_succ]
      exact AElem_pow_three
    exact eq_inv_of_mul_eq_one_left h3
  rw [hrel, ha2, mul_inv_cancel_right]

theorem P3_map
    (α : MulAut ↥mclP) (hα : U9.map α.toMonoidHom = U9) : P3.map α.toMonoidHom = P3 := by
  obtain ⟨x, hxconj, hxp0⟩ := conj_fixes_p0 α hα
  have hxp0' : x p0 = p0 := hxp0
  have hxO2 := x_smul_O2 α hα hxconj
  have hxS : x • S3 = S3 := smul_S_of x hxp0' hxO2
  have hxSinv : x⁻¹ • S3 = S3 := by
    calc x⁻¹ • S3 = x⁻¹ • (x • S3) := by rw [hxS]
      _ = S3 := by rw [smul_smul, inv_mul_cancel, one_smul]
  have hle : P3.map α.toMonoidHom ≤ P3 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_P3_iff] at hg ⊢
    refine ⟨?_, ?_⟩
    · let ht0 : ↥mclP := ⟨mclT0, mclT0_facts.1⟩
      have hfix_t0 : α ht0 = ht0 := by simpa [ht0] using map_t0 α hα
      have hgcomm : g * ht0 = ht0 * g := by
        apply Subtype.ext
        simpa [ht0] using (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg.1).2
          mclT0 (by simp)).symm
      have hcommα : α g * α ht0 = α ht0 * α g := by
        rw [← map_mul, hgcomm, map_mul]
      rw [hfix_t0] at hcommα
      refine ⟨(α g).2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [ht0] using congrArg Subtype.val hcommα)
    · have hconj : ((MulEquiv.toMonoidHom α) g).val = x * g.val * x⁻¹ := hxconj g
      rw [hconj]
      calc (x * g.val * x⁻¹) • S3 = x • (g.val • (x⁻¹ • S3)) := by rw [mul_smul, mul_smul]
        _ = x • (g.val • S3) := by rw [hxSinv]
        _ = x • S3 := by rw [hg.2]
        _ = S3 := hxS
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]

theorem package744105 :
    ∃ (U P : Subgroup ↥CFSG.Sporadic.Schreier.mclP)
      (a g : ↥CFSG.Sporadic.Schreier.mclP),
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ Nat.card P = 3 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Schreier.mclP,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      a ∈ P ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧ g * a * g⁻¹ = a⁻¹ := by
  refine ⟨U9, P3, AElem, GElem, ?_, U9_le_P3, P3_card, fun α hα => P3_map α hα, AElem_mem_P3,
    AElem_ne_one, AElem_pow_three, GElem_inv⟩
  refine ⟨le_top, IsPGroup.of_card (n := 7) (by rw [U9_card]; norm_num), ?_⟩
  have h_top : Nat.card (⊤ : Subgroup ↥mclP) = 898128000 := by
    rw [Subgroup.card_top, card_mclP]
  have h_mul : Nat.card U9 * (U9.subgroupOf ⊤).index = 898128000 := by
    have := Subgroup.card_mul_index (H := U9.subgroupOf ⊤)
    rw [h_top] at this
    simpa [card_subgroupOf_of_le (le_top : U9 ≤ ⊤)] using this
  have h_index : (U9.subgroupOf ⊤).index = 7016625 := by
    rw [U9_card] at h_mul
    omega
  rw [h_index]
  norm_num

end CertificateChecks.KernelSpor.McLThree

end
