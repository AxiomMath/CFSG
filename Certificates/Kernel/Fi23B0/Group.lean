module

public import Certificates.Kernel.Fi23B0.Glue

public section

namespace CertificateChecks.KernelFi23B0

open CFSG.KD.Fi23B0 CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_stab {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) (p : X) :
    Nat.card (MulAction.stabilizer H p) = Nat.card (H ⊓ MulAction.stabilizer G p : Subgroup G) :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem orbit_stab {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) (p : X) :
    Nat.card H = Nat.card (MulAction.orbit H p) *
      Nat.card (H ⊓ MulAction.stabilizer G p : Subgroup G) := by
  have h1 := (MulAction.stabilizer H p).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, card_stab] at h1
  rw [← h1, mul_comm]


abbrev zP : Fin 31671 := ⟨2776, by norm_num⟩
abbrev uP : Fin 31671 := ⟨14566, by norm_num⟩
abbrev vP : Fin 31671 := ⟨18249, by norm_num⟩
abbrev xP : Fin 31671 := ⟨28381, by norm_num⟩
abbrev oP : Fin 31671 := ⟨0, by norm_num⟩
abbrev iP : Fin 31671 := ⟨1, by norm_num⟩

abbrev S3 : Finset (Fin 31671) := {zP, uP, vP}

theorem smul_eq_of_idx {g : J} {a b : Fin 31671} (h : idx 31671 g a.val = b.val) : g • a = b :=
  Fin.ext (by rw [← idx_of_lt g a.isLt]; exact h)

theorem mem_S3 (p : Fin 31671) : p ∈ S3 ↔ InS p.val := by
  simp only [S3, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

noncomputable abbrev B : Subgroup J := MulAction.stabilizer J S3

theorem mem_B_of {g : J} (h : ∀ p ∈ S3, g • p ∈ S3) : g ∈ B := by
  rw [MulAction.mem_stabilizer_iff]
  refine Finset.eq_of_subset_of_card_le ?_ (Finset.card_smul_finset g S3).ge
  intro b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hb
  exact h x hx

theorem smul_mem_of_B {g : J} (hg : g ∈ B) {p : Fin 31671} (hp : p ∈ S3) : g • p ∈ S3 := by
  rw [← MulAction.mem_stabilizer_iff.1 hg]
  exact Finset.smul_mem_smul_finset hp

theorem mem_B_of_idx {g : J} (h : ∀ p, InS p → InS (idx 31671 g p)) : g ∈ B := by
  apply mem_B_of
  intro p hp
  rw [mem_S3] at hp ⊢
  rw [← idx_of_lt g p.isLt]
  exact h _ hp

theorem mem_cent_of_idx {g : J} (hg : idx 31671 g 2776 = 2776) :
    g ∈ Subgroup.centralizer ({conjPt 2776} : Set J) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := (idx_eq_iff (g := g) (by norm_num : 2776 < 31671) (by norm_num : 2776 < 31671)).1 hg
  calc g * conjPt 2776 = g * conjPt 2776 * g⁻¹ * g := by group
    _ = conjPt 2776 * g := by rw [h]

theorem idx_of_cent {g : J} (hg : g ∈ Subgroup.centralizer ({conjPt 2776} : Set J)) :
    idx 31671 g 2776 = 2776 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  refine (idx_eq_iff (g := g) (by norm_num : 2776 < 31671) (by norm_num : 2776 < 31671)).2 ?_
  rw [hg, mul_inv_cancel_right]

theorem slvl_le {K : Subgroup J} (h : ∀ j < 21, sylG j ∈ K) : slvl 0 ≤ K := by
  rw [slvl, levelGroup, lettersGroup, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_levelLetters_zero, LS_size, sylWords_size] at hl
  have hmem := h (l / 2) (by omega)
  unfold pairG
  split_ifs
  · exact hmem
  · exact K.inv_mem hmem

theorem slvl_le_B : slvl 0 ≤ B := slvl_le fun j hj => mem_B_of_idx (syl_facts.1 j hj).2

theorem slvl_le_cent : slvl 0 ≤ Subgroup.centralizer ({conjPt 2776} : Set J) :=
  slvl_le fun j hj => mem_cent_of_idx (syl_facts.1 j hj).1

noncomputable abbrev mv : J := wordG jG moverW

theorem mv_mem : mv ∈ B := by
  obtain ⟨h1, h2, h3⟩ := mover_facts
  refine mem_B_of_idx fun p hp => ?_
  rcases hp with rfl | rfl | rfl
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inl rfl
  · rw [h3]; exact Or.inr (Or.inr rfl)

theorem not_B_le_cent : ¬ B ≤ Subgroup.centralizer ({conjPt 2776} : Set J) := by
  intro h
  have := idx_of_cent (h mv_mem)
  rw [mover_facts.1] at this
  exact absurd this (by norm_num)

noncomputable abbrev s1 : J := sylG 1

theorem s1_mem : s1 ∈ B := mem_B_of_idx (syl_facts.1 1 (by norm_num)).2

theorem s1_z : s1 • zP = zP := smul_eq_of_idx (syl_facts.1 1 (by norm_num)).1
theorem s1_u : s1 • uP = vP := smul_eq_of_idx syl_facts.2.1
theorem mv_z : mv • zP = uP := smul_eq_of_idx mover_facts.1

theorem card_orbit_z : Nat.card (MulAction.orbit B zP) = 3 := by
  have hO : MulAction.orbit B zP = (S3 : Set (Fin 31671)) := by
    ext q
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      exact smul_mem_of_B hg (by simp [S3])
    · intro hq
      simp only [S3, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact ⟨⟨mv, mv_mem⟩, mv_z⟩
      · refine ⟨⟨s1 * mv, B.mul_mem s1_mem mv_mem⟩, ?_⟩
        change (s1 * mv) • zP = vP
        rw [mul_smul, mv_z, s1_u]
  rw [hO, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

noncomputable abbrev B1 : Subgroup J := B ⊓ MulAction.stabilizer J zP

theorem card_orbit_u : Nat.card (MulAction.orbit B1 uP) = 2 := by
  have hO : MulAction.orbit B1 uP = ({uP, vP} : Set (Fin 31671)) := by
    ext q
    constructor
    · rintro ⟨⟨g, hgB, hgz⟩, rfl⟩
      have hz : g • zP = zP := hgz
      change g • uP ∈ _
      have hm := (mem_S3 _).1 (smul_mem_of_B hgB (by simp [S3] : uP ∈ S3))
      have hne : g • uP ≠ zP := by
        intro e
        rw [← hz] at e
        exact absurd (smul_left_cancel g e) (by decide)
      rcases hm with h | h | h
      · exact absurd (Fin.ext h) hne
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    · rintro (rfl | rfl)
      · exact MulAction.mem_orbit_self _
      · exact ⟨⟨s1, s1_mem, s1_z⟩, s1_u⟩
  rw [hO, Nat.card_coe_set_eq, Set.ncard_pair (by decide)]

noncomputable abbrev K3 : Subgroup J :=
  MulAction.stabilizer J zP ⊓ MulAction.stabilizer J uP ⊓ MulAction.stabilizer J vP

theorem B2_eq : B1 ⊓ MulAction.stabilizer J uP = K3 := by
  ext g
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨⟨hgB, hz⟩, hu⟩
    refine ⟨⟨hz, hu⟩, ?_⟩
    have hm := (mem_S3 _).1 (smul_mem_of_B hgB (by simp [S3] : vP ∈ S3))
    rcases hm with h | h | h
    · have e : g • vP = g • zP := by rw [hz]; exact Fin.ext h
      exact absurd (smul_left_cancel g e) (by decide)
    · have e : g • vP = g • uP := by rw [hu]; exact Fin.ext h
      exact absurd (smul_left_cancel g e) (by decide)
    · exact Fin.ext h
  · rintro ⟨⟨hz, hu⟩, hv⟩
    refine ⟨⟨mem_B_of fun p hp => ?_, hz⟩, hu⟩
    simp only [S3, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · rw [hz]; simp [S3]
    · rw [hu]; simp [S3]
    · rw [hv]; simp [S3]

noncomputable abbrev L3 : Subgroup J :=
  MulAction.stabilizer J oP ⊓ MulAction.stabilizer J iP ⊓ MulAction.stabilizer J xP

noncomputable abbrev cc : J := wordG jG gW

theorem cc_o : cc • oP = zP := smul_eq_of_idx conj_facts.1
theorem cc_i : cc • iP = uP := smul_eq_of_idx conj_facts.2.1
theorem cc_x : cc • xP = vP := smul_eq_of_idx conj_facts.2.2

theorem conj_fix {g : J} {a b : Fin 31671} (hab : cc • a = b) :
    (cc⁻¹ * g * cc) • a = a ↔ g • b = b := by
  have ha : a = cc⁻¹ • b := by rw [← hab, inv_smul_smul]
  rw [mul_smul, mul_smul, hab, ha, inv_smul_eq_iff, smul_inv_smul]

theorem card_K3 : Nat.card K3 = Nat.card L3 :=
  Nat.card_congr
    { toFun := fun g => ⟨cc⁻¹ * g.1 * cc, by
        obtain ⟨⟨hz, hu⟩, hv⟩ := g.2
        exact ⟨⟨(conj_fix cc_o).2 hz, (conj_fix cc_i).2 hu⟩, (conj_fix cc_x).2 hv⟩⟩
      invFun := fun g => ⟨cc * g.1 * cc⁻¹, by
        obtain ⟨⟨h0, h1⟩, hx⟩ := g.2
        have e : cc⁻¹ * (cc * g.1 * cc⁻¹) * cc = g.1 := by group
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact (conj_fix cc_o).1 (by rw [e]; exact h0)
        · exact (conj_fix cc_i).1 (by rw [e]; exact h1)
        · exact (conj_fix cc_x).1 (by rw [e]; exact hx)⟩
      left_inv := fun g => Subtype.ext (by simp only; group)
      right_inv := fun g => Subtype.ext (by simp only; group) }

theorem mem_lvl_two_iff (g : J) : g ∈ lvl 2 ↔ idx 31671 g 0 = 0 ∧ idx 31671 g 1 = 1 := by
  have hb := chain_facts'.2.1 1 (by rw [chainBase_size]; norm_num)
  constructor
  · intro h
    have h1 : g ∈ lvl 1 := levelGroup_anti (pairG gs) (by norm_num : 1 ≤ 2) h
    refine ⟨(lvl_one_iff g).2 h1, ?_⟩
    have := (hb g h1).2 h
    rwa [chainBase_one] at this
  · rintro ⟨h0, h1⟩
    exact (hb g ((lvl_one_iff g).1 h0)).1 (by rw [chainBase_one]; exact h1)

theorem L3_eq : L3 = lvl 2 ⊓ MulAction.stabilizer J xP := by
  ext g
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, mem_lvl_two_iff,
    idx_of_lt g (by norm_num : 0 < 31671), idx_of_lt g (by norm_num : 1 < 31671), Fin.ext_iff]

theorem card_lvl_two : Nat.card (lvl 2) = 36787322880 := by
  rw [chain_facts'.2.2 2 (by rw [chainBase_size]; norm_num), chainBase_size,
    show Finset.Ico 2 6 = {2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    tree_size_of (l := 2) rfl, tree_size_of (l := 3) rfl, tree_size_of (l := 4) rfl,
    tree_size_of (l := 5) rfl]
  norm_num

theorem card_L3 : Nat.card L3 = 53084160 := by
  have h := orbit_stab (lvl 2) xP
  rw [card_lvl_two, card_orbit_two, ← L3_eq] at h
  omega

theorem card_B : Nat.card B = 318504960 := by
  have h1 := orbit_stab B zP
  have h2 := orbit_stab B1 uP
  rw [card_orbit_z] at h1
  rw [card_orbit_u, B2_eq, card_K3, card_L3] at h2
  rw [h1, h2]

theorem b0_exists : ∃ B : Subgroup J, slvl 0 ≤ B ∧
    slvl 0 ≤ Subgroup.centralizer ({conjPt 2776} : Set J) ∧ Nat.card B = 318504960 ∧
    ¬ B ≤ Subgroup.centralizer ({conjPt 2776} : Set J) :=
  ⟨B, slvl_le_B, slvl_le_cent, card_B, not_B_le_cent⟩

end CertificateChecks.KernelFi23B0

end
