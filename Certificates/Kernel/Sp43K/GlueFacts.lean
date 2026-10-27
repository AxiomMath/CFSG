module

public import Certificates.Kernel.Sp43K.GlueCard
public import CFSG.Certificates.Kernel.Sp43KGrpFacts

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K CFSG.Sp43 Subgroup

@[expose] noncomputable def Mk (j : ℕ) : Subgroup G := sub2T (hA j) (hB j)

theorem mk_lt {i : ℕ} (hi : i < 5) : Mk i = sub2T (gA i) (gB i) := by
  rw [Mk, hA, hB, if_pos hi, if_pos hi]

theorem mem_mk_of_fld {i t c : ℕ} (hi : i < 5) (ht : t < ords.getD i 0)
    (h : fldT (mP i) t = c) : ofT c ∈ Mk i := by
  rw [mk_lt hi]
  exact ((lst_member hi).2.2.2.2.1 _).2 ⟨t, ht, by rw [h]⟩

theorem inG_of_fld {i t c : ℕ} (hi : i < 5) (ht : t < ords.getD i 0)
    (h : fldT (mP i) t = c) : okT c = true ∧ InG c := by
  rw [← h]
  exact (lst_member hi).2.2.1 t ht

theorem card_mk {i : ℕ} (hi : i < 5) : Nat.card (Mk i) = ords.getD i 0 := by
  rw [mk_lt hi]
  exact (lst_member hi).2.2.2.2.2

theorem normC_all : ∀ i < 5, normC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1322001n_0, ch1322001n_1, ch1322001n_2, ch1322001n_3, ch1322001n_4]

@[expose] noncomputable def nsI (i : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) := ns.getD i ((0, 0), (0, 0))

theorem normC_spec {i : ℕ} (hi : i < 5) :
    InG (nsI i).1.1 ∧ InG (nsI i).1.2 ∧ InG (nsI i).2.1 ∧ InG (nsI i).2.2 ∧
      mulT (nsI i).1.1 (nsI i).1.2 = oneT ∧ mulT (nsI i).2.1 (nsI i).2.2 = oneT ∧
      ofT (nsI i).1.1 ∈ normalizer (Mk i : Set G) ∧ ofT (nsI i).2.1 ∈ normalizer (Mk i : Set G) := by
  have h := normC_all i hi
  unfold normC normK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ :=
    h
  obtain ⟨-, -, s1, s2, s3, s4, -⟩ := spC_spec (spC_all i hi)
  obtain ⟨hA', hB', -⟩ := lst_member hi
  have n1 := inG_of_spT h1 s1
  have n2 := inG_of_spT h2 s2
  have n3 := inG_of_spT h3 s3
  have n4 := inG_of_spT h4 s4
  refine ⟨n1, n2, n3, n4, h5, h6, ?_, ?_⟩
  · rw [mk_lt hi]
    exact mem_normalizer_sub2T hA' hB' n1 n2 h5
      (by rw [← mk_lt hi]; exact mem_mk_of_fld hi h7 h8)
      (by rw [← mk_lt hi]; exact mem_mk_of_fld hi h9 h10)
  · rw [mk_lt hi]
    exact mem_normalizer_sub2T hA' hB' n3 n4 h6
      (by rw [← mk_lt hi]; exact mem_mk_of_fld hi h11 h12)
      (by rw [← mk_lt hi]; exact mem_mk_of_fld hi h13 h14)

theorem normGens_le {i : ℕ} (hi : i < 5) :
    sub2T (nsI i).1.1 (nsI i).2.1 ≤ normalizer (Mk i : Set G) := by
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := normC_spec hi
  rw [sub2T, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact h1
  · exact h2

theorem g5C_spec : okT G5.1 = true ∧ okT G5.2.1 = true ∧ okT G5.2.2.1 = true ∧
    okT G5.2.2.2 = true ∧ mulT G5.1 G5.2.2.1 = oneT ∧ mulT G5.2.1 G5.2.2.2 = oneT := by
  have h := ch1322001g50
  unfold g5C at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem inG_G5 : InG G5.1 ∧ InG G5.2.1 ∧ InG G5.2.2.1 ∧ InG G5.2.2.2 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := g5C_spec
  obtain ⟨s1, s2, s3, s4, -⟩ := sp5C_spec
  exact ⟨inG_of_spT h1 s1, inG_of_spT h2 s2, inG_of_spT h3 s3, inG_of_spT h4 s4⟩

theorem wdC_spec : wordT G5.1 G5.2.1 (wd.getD 0 []) = p0.1 ∧
    wordT G5.1 G5.2.1 (wd.getD 1 []) = p0.2 ∧ wordT G5.1 G5.2.1 (wd.getD 2 []) = gA 4 ∧
    wordT G5.1 G5.2.1 (wd.getD 3 []) = gB 4 := by
  have h := ch1322001wd0
  unfold wdC at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem mk_five_eq : Mk 5 = sub2T G5.1 G5.2.1 := by
  rw [Mk, hA, hB, if_neg (by norm_num), if_neg (by norm_num)]

theorem mk_five : Mk 5 = ⊤ := by
  obtain ⟨g1, g2, -⟩ := inG_G5
  obtain ⟨w1, w2, w3, w4⟩ := wdC_spec
  have hle : ∀ {c d : ℕ}, ofT c ∈ Mk 5 → ofT d ∈ Mk 5 → sub2T c d ≤ Mk 5 := by
    intro c d hc hd
    rw [sub2T, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hc
    · exact hd
  have hw : ∀ k, ofT (wordT G5.1 G5.2.1 (wd.getD k [])) ∈ Mk 5 := by
    intro k
    rw [mk_five_eq]
    exact (wordT_mem g1 g2 _).2
  have hP : sub2T p0.1 p0.2 ≤ Mk 5 := hle (w1 ▸ hw 0) (w2 ▸ hw 1)
  have h4 : sub2T (gA 4) (gB 4) ≤ Mk 5 := hle (w3 ▸ hw 2) (w4 ▸ hw 3)
  have d81 : 81 ∣ Nat.card (Mk 5) := by
    rw [← lst_p0.2.2.2.2.2]
    exact Subgroup.card_dvd_of_le hP
  have d1920 : 1920 ∣ Nat.card (Mk 5) := by
    have e : ords.getD 4 0 = 1920 := rfl
    rw [← e, ← (lst_member (i := 4) (by norm_num)).2.2.2.2.2]
    exact Subgroup.card_dvd_of_le h4
  have e : Nat.lcm 81 1920 = 51840 := by norm_num
  have hl := Nat.lcm_dvd d81 d1920
  rw [e] at hl
  have hle' : Nat.card (Mk 5) ≤ Nat.card G := Subgroup.card_le_card_group _
  rw [card_G] at hle'
  apply Subgroup.eq_top_of_card_eq
  rw [card_G]
  exact le_antisymm hle' (Nat.le_of_dvd Nat.card_pos hl)

theorem three : ∃ z ∈ Mk 3, z ∈ center G ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
  have h := ch1322001h30
  unfold h3C at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨e, ht⟩, hf⟩ := h
  have hm : InG minusT := inG_of_spT okT_minusT (by
    have := sp5C_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rwa [e] at this)
  refine ⟨ofT minusT, ?_, minusT_center hm, minusT_ne_one hm, minusT_sq hm⟩
  exact mem_mk_of_fld (i := 3) (by norm_num) ht (by rw [hf, e]; rfl)

theorem four : ∃ a ∈ Mk 4, a ^ 3 = 1 ∧ a ≠ 1 ∧ ∃ U : Subgroup G, U ≤ Mk 4 ∧ Nat.card U = 48 ∧
    ∀ u ∈ U, u * a * u⁻¹ ∈ zpowers a := by
  have h := ch1322001h40
  unfold h4C at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpo, hp1⟩, hp3⟩, hq1⟩, hfp⟩, hq2⟩, hfu⟩, hq3⟩, hfv⟩, hou'⟩, hov'⟩,
    hui⟩, hvi⟩, hcu⟩, hcv⟩, hlst⟩ := h
  have e4 : ords.getD 4 0 = 1920 := rfl
  obtain ⟨-, hp⟩ := inG_of_fld (i := 4) (by norm_num) (e4 ▸ hq1) hfp
  obtain ⟨huo, hu⟩ := inG_of_fld (i := 4) (by norm_num) (e4 ▸ hq2) hfu
  obtain ⟨hvo, hv⟩ := inG_of_fld (i := 4) (by norm_num) (e4 ▸ hq3) hfv
  have hu' := inG_of_spT hou' sp5C_spec.2.2.2.2.2.2.2.2.2.1
  have hv' := inG_of_spT hov' sp5C_spec.2.2.2.2.2.2.2.2.2.2.1
  have hpM := mem_mk_of_fld (i := 4) (by norm_num) (e4 ▸ hq1) hfp
  have huM := mem_mk_of_fld (i := 4) (by norm_num) (e4 ▸ hq2) hfu
  have hvM := mem_mk_of_fld (i := 4) (by norm_num) (e4 ▸ hq3) hfv
  set a := ofT h4.1
  have ha3 : a ^ 3 = 1 := by
    rw [pow_three', ← ofT_mulT hp hp, ← ofT_mulT (inG_mulT hp hp) hp, hp3, ofT_oneT]
  have ha1 : a ≠ 1 := by
    intro e
    rw [← ofT_oneT] at e
    exact hp1 (ofT_inj hp inG_oneT hpo (by decide) e)
  have hconj : ∀ {n n' : ℕ}, InG n → InG n' → mulT n n' = oneT →
      (conjT n n' h4.1 = h4.1 ∨ conjT n n' h4.1 = mulT h4.1 h4.1) →
      ofT n ∈ normalizer (zpowers a : Set G) := by
    intro n n' hn hn' hnn hc
    rw [Subgroup.zpowers_eq_closure]
    apply mem_normalizer_of_conj (s := {a})
    rintro k rfl
    rw [← ofT_conjT hn hn' hp hnn]
    rcases hc with hc | hc
    · rw [hc]
      exact Subgroup.subset_closure rfl
    · rw [hc, ofT_mulT hp hp]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure rfl) (Subgroup.subset_closure rfl)
  obtain ⟨-, -, -, hcard⟩ := lst_spec (R := fun i => uvR.getD (i - 0) (0, 0, 0, 0)) hu hv
    (by norm_num) fun i hi => ((lstK_spec hlst).2.2 i (Nat.zero_le i) hi).2
  refine ⟨a, hpM, ha3, ha1, sub2T h4.2.1 h4.2.2.1, ?_, hcard, ?_⟩
  · rw [sub2T, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact huM
    · exact hvM
  · intro w hw
    have hN : sub2T h4.2.1 h4.2.2.1 ≤ normalizer (zpowers a : Set G) := by
      rw [sub2T, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hconj hu hu' hui hcu
      · exact hconj hv hv' hvi hcv
    exact (Subgroup.mem_normalizer_iff.1 (hN hw) a).1 (Subgroup.mem_zpowers a)

theorem sylow5 : ∃ D₀ : Sylow 5 G, (D₀ : Subgroup G) = Mk 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : Nat.card (Mk 0) = 5 := card_mk (i := 0) (by norm_num)
  have hp : IsPGroup 5 (Mk 0) := IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  have hidx : (Mk 0).index = 10368 := by
    have := Subgroup.card_mul_index (Mk 0)
    rw [hc, card_G] at this
    omega
  exact ⟨hp.toSylow (by rw [hidx]; norm_num), rfl⟩

theorem normD : ∃ D : Sylow 5 G, 40 ≤ Nat.card (normalizer (D : Set G)) := by
  obtain ⟨D₀, hD₀⟩ := sylow5
  refine ⟨D₀, ?_⟩
  have h := ch1322001n00
  unfold n0C at h
  obtain ⟨ho1, ho2, hall⟩ := lstK_spec h
  obtain ⟨n1, -, n3, -⟩ := normC_spec (i := 0) (by norm_num)
  have h40 := (lst_spec (R := fun i => nR.getD (i - 0) (0, 0, 0, 0)) n1 n3 (by norm_num)
    fun i hi => (hall i (Nat.zero_le i) hi).2).2.2.2
  change 40 ≤ Nat.card (normalizer ((D₀ : Subgroup G) : Set G))
  rw [hD₀, ← h40]
  exact Subgroup.card_le_of_le (normGens_le (i := 0) (by norm_num))

theorem sylow3 : ∃ P₀ : Sylow 3 G, (P₀ : Subgroup G) = sub2T p0.1 p0.2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := lst_p0.2.2.2.2.2
  have hp : IsPGroup 3 (sub2T p0.1 p0.2) := IsPGroup.of_card (n := 4) (by rw [hc]; norm_num)
  have hidx : (sub2T p0.1 p0.2).index = 640 := by
    have := Subgroup.card_mul_index (sub2T p0.1 p0.2)
    rw [hc, card_G] at this
    omega
  exact ⟨hp.toSylow (by rw [hidx]; norm_num), rfl⟩

theorem bq_lt {k : ℕ} (hall : (bq.all fun q => decide (q < 81)) = true) (hk : k < bq.length) :
    bq.getD k 0 < 81 := by
  rw [List.all_eq_true] at hall
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact of_decide_eq_true (hall _ (List.getElem_mem hk))

theorem normP : ∃ P : Sylow 3 G, 324 ≤ Nat.card (normalizer (P : Set G)) := by
  obtain ⟨P₀, hP₀⟩ := sylow3
  refine ⟨P₀, ?_⟩
  have h := ch1322001b0
  unfold bC at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho1, ho2⟩, hm1⟩, hm2⟩, hlst⟩, hlen⟩, hall⟩, e1⟩, e2⟩, e3⟩, e4⟩ := h
  obtain ⟨hb1o, hb2o, hpos⟩ := lstK_spec hlst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, sb1, sb2, sb3, sb4, -⟩ := sp5C_spec
  have b1 := inG_of_spT hb1o sb1
  have b2 := inG_of_spT hb2o sb2
  have b3 := inG_of_spT ho1 sb3
  have b4 := inG_of_spT ho2 sb4
  obtain ⟨p1, p2, -, -, hiff, -⟩ := lst_p0
  have hmem : ∀ {k c : ℕ}, k < 4 → fldT p0P (bq.getD k 0) = c → ofT c ∈ sub2T p0.1 p0.2 := by
    intro k c hk e
    exact (hiff _).2 ⟨_, bq_lt hall (by rw [hlen]; exact hk), by rw [e]⟩
  have hN : sub2T b.1 b.2.1 ≤ normalizer (sub2T p0.1 p0.2 : Set G) := by
    rw [sub2T, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mem_normalizer_sub2T p1 p2 b1 b3 hm1 (hmem (k := 0) (by norm_num) e1)
        (hmem (k := 1) (by norm_num) e2)
    · exact mem_normalizer_sub2T p1 p2 b2 b4 hm2 (hmem (k := 2) (by norm_num) e3)
        (hmem (k := 3) (by norm_num) e4)
  have h324 := (lst_spec (R := fun i => bR.getD (i - 0) (0, 0, 0, 0)) b1 b2 (by norm_num)
    fun i hi => (hpos i (Nat.zero_le i) hi).2).2.2.2
  change 324 ≤ Nat.card (normalizer ((P₀ : Subgroup G) : Set G))
  rw [hP₀, ← h324]
  exact Subgroup.card_le_of_le hN

end CFSG.KD.Sp43K

end
