module

public import Certificates.Kernel.Sp43K.GlueOrb
public import Certificates.Kernel.Sp43K.Syl
public import CFSG.Certificates.Kernel.Sp43KSylSound
public import CFSG.Certificates.Kernel.Sp43KGen

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K CFSG.Sp43 CFSG.Sp43.Native Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem sylC_all : ∀ j < 8, sylC j = true := by
  intro j hj
  interval_cases j
  exacts [ch1322001s_0, ch1322001s_1, ch1322001s_2, ch1322001s_3, ch1322001s_4, ch1322001s_5,
    ch1322001s_6, ch1322001s_7]

theorem sylC_parts {j : ℕ} (hj : j < 8) : dO.length = 1296 ∧
    sylGo (gA 0) ((dO.drop (162 * j)).take 162)
      (if j = 0 then 0 else keyT (gA 0) (dO.getD (162 * j - 1) (0, 0)).1
        (dO.getD (162 * j - 1) (0, 0)).2) = true := by
  have h := sylC_all j hj
  unfold sylC at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

theorem dO_len : dO.length = 1296 := (sylC_parts (j := 0) (by norm_num)).1

theorem dO_facts : ∀ m < 1296, okT (dO.getD m (0, 0)).1 = true ∧ okT (dO.getD m (0, 0)).2 = true ∧
    spT (dO.getD m (0, 0)).1 = true ∧ mulT (dO.getD m (0, 0)).1 (dO.getD m (0, 0)).2 = oneT := by
  intro m hm
  obtain ⟨-, h⟩ := sylC_parts (j := m / 162) (by omega)
  have hs : 162 * (m / 162) ≤ m := Nat.mul_div_le m 162
  have := (sylGo_spec _ _ h).1 (m - 162 * (m / 162)) (by
    rw [List.length_take, List.length_drop, dO_len]
    omega)
  rwa [getD_chunk _ _ hs (by omega)] at this

@[expose] noncomputable def kD (m : ℕ) : ℕ := keyT (gA 0) (dO.getD m (0, 0)).1 (dO.getD m (0, 0)).2

theorem kD_lt : ∀ m, m + 1 < 1296 → kD m < kD (m + 1) := by
  intro m hm
  by_cases hb : (m + 1) % 162 = 0
  · obtain ⟨-, h⟩ := sylC_parts (j := (m + 1) / 162) (by omega)
    have hj0 : (m + 1) / 162 ≠ 0 := by omega
    have e1 : 162 * ((m + 1) / 162) - 1 = m := by omega
    rw [if_neg hj0, e1] at h
    have := (sylGo_spec _ _ h).2.1 (by
      intro h'
      have := congrArg List.length h'
      rw [List.length_take, List.length_drop, dO_len] at this
      simp at this
      omega)
    have e2 : 162 * ((m + 1) / 162) = m + 1 := by omega
    have e3 := getD_chunk dO (0, 0) (le_refl (m + 1)) (by omega : m + 1 < m + 1 + 162)
    rw [Nat.sub_self] at e3
    rw [e2, e3] at this
    exact this
  · obtain ⟨-, h⟩ := sylC_parts (j := m / 162) (by omega)
    have hs : 162 * (m / 162) ≤ m := Nat.mul_div_le m 162
    have := (sylGo_spec _ _ h).2.2 (m - 162 * (m / 162)) (by
      rw [List.length_take, List.length_drop, dO_len]
      omega)
    have e : m - 162 * (m / 162) + 1 = m + 1 - 162 * (m / 162) := by omega
    rw [getD_chunk _ _ hs (by omega), e, getD_chunk _ _ (by omega) (by omega)] at this
    exact this

theorem kD_inj {m m' : ℕ} (hm : m < 1296) (hm' : m' < 1296) (h : kD m = kD m') : m = m' := by
  have hlt : ∀ j, ∀ i, i < j → j < 1296 → kD i < kD j := by
    intro j
    induction j with
    | zero => intro i hij; omega
    | succ j ih =>
      intro i hij hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih i h' (by omega)).trans (kD_lt j hj)
      · exact kD_lt i hj
  rcases lt_trichotomy m m' with h1 | h1 | h1
  · exact absurd h (hlt m' m h1 hm').ne
  · exact h1
  · exact absurd h.symm (hlt m m' h1 hm).ne

theorem gA0_ne : gA 0 ≠ oneT := by
  have h : (gA 0 != oneT) = true := by decide +kernel
  simpa using h

theorem d_order : orderOf (ofT (gA 0)) = 5 ∧ zpowers (ofT (gA 0)) = Mk 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hA', -, ho, -⟩ := lst_member (i := 0) (by norm_num)
  have hc : Nat.card (Mk 0) = 5 := card_mk (i := 0) (by norm_num)
  have hmem : ofT (gA 0) ∈ Mk 0 := by
    rw [mk_lt (by norm_num)]
    exact Subgroup.subset_closure (by simp)
  have hle : zpowers (ofT (gA 0)) ≤ Mk 0 := (Subgroup.zpowers_le).2 hmem
  have hne : ofT (gA 0) ≠ 1 := by
    intro e
    rw [← ofT_oneT] at e
    have hok : okT (gA 0) = true := by
      have h := memC_all 0 (by norm_num)
      unfold memC at h
      have e0 : jobs.getD 0 (0, 0) = (0, 0) := by decide
      rw [e0] at h
      dsimp only at h
      unfold memPart at h
      exact (lstK_spec h).1
    exact gA0_ne (ofT_inj hA' inG_oneT hok (by decide) e)
  have hdvd : orderOf (ofT (gA 0)) ∣ 5 := by
    rw [← hc]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  have h5 : orderOf (ofT (gA 0)) = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  refine ⟨h5, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [hc, Nat.card_zpowers, h5]

theorem card_normalizer_D₀ : Nat.card (normalizer (Mk 0 : Set G)) ≤ 40 := by
  obtain ⟨hd5, hz⟩ := d_order
  have hd : InG (gA 0) := (lst_member (i := 0) (by norm_num)).1
  set N := normalizer (Mk 0 : Set G)
  have hgo : ∀ m < 1296, InG (dO.getD m (0, 0)).1 ∧ InG (dO.getD m (0, 0)).2 := by
    intro m hm
    obtain ⟨o1, o2, s1, e⟩ := dO_facts m hm
    have h1 := inG_of_spT o1 s1
    exact ⟨h1, inG_of_mulT_one h1 (okT_spec o2).1 e⟩
  let f : Fin 1296 → G ⧸ N := fun m => QuotientGroup.mk (ofT (dO.getD m (0, 0)).1)
  have hinj : Function.Injective f := by
    intro m m' e
    have e' := QuotientGroup.eq.1 e
    have hmap : (Mk 0).map (MulAut.conj ((ofT (dO.getD m (0, 0)).1)⁻¹ *
        ofT (dO.getD m' (0, 0)).1)).toMonoidHom = Mk 0 :=
      CFSG.Sp43.map_conj_eq_of_mem_normalizer e'
    have hconj : (zpowers (ofT (gA 0))).map (MulAut.conj (ofT (dO.getD m (0, 0)).1)).toMonoidHom =
        (zpowers (ofT (gA 0))).map (MulAut.conj (ofT (dO.getD m' (0, 0)).1)).toMonoidHom := by
      rw [hz]
      calc (Mk 0).map (MulAut.conj (ofT (dO.getD m (0, 0)).1)).toMonoidHom
          = ((Mk 0).map (MulAut.conj ((ofT (dO.getD m (0, 0)).1)⁻¹ *
              ofT (dO.getD m' (0, 0)).1)).toMonoidHom).map
              (MulAut.conj (ofT (dO.getD m (0, 0)).1)).toMonoidHom := by rw [hmap]
        _ = _ := by rw [CFSG.Sp43.map_conj_map_conj, mul_inv_cancel_left]
    obtain ⟨a1, a2⟩ := hgo m m.2
    obtain ⟨b1, b2⟩ := hgo m' m'.2
    exact Fin.ext (kD_inj m.2 m'.2 (keyT_eq_of_conj hd hd5 a1 a2 (dO_facts m m.2).2.2.2 b1 b2
      (dO_facts m' m'.2).2.2.2 hconj))
  have hidx : 1296 ≤ N.index := by
    rw [Subgroup.index]
    calc 1296 = Nat.card (Fin 1296) := (Nat.card_fin 1296).symm
      _ ≤ Nat.card (G ⧸ N) := Nat.card_le_card_of_injective f hinj
  have hmul := Subgroup.card_mul_index N
  rw [card_G] at hmul
  nlinarith

theorem normalizer_D₀ : normalizer (Mk 0 : Set G) = sub2T (nsI 0).1.1 (nsI 0).2.1 := by
  have h := ch1322001n00
  unfold n0C at h
  obtain ⟨-, -, hall⟩ := lstK_spec h
  obtain ⟨n1, -, n3, -⟩ := normC_spec (i := 0) (by norm_num)
  have h40 := (lst_spec (R := fun i => nR.getD (i - 0) (0, 0, 0, 0)) n1 n3 (by norm_num)
    fun i hi => (hall i (Nat.zero_le i) hi).2).2.2.2
  symm
  apply Subgroup.eq_of_le_of_card_ge (normGens_le (i := 0) (by norm_num))
  rw [h40]
  exact card_normalizer_D₀

theorem normalizer_D₀_noEig : ∀ x ∈ normalizer (Mk 0 : Set G),
    x = 1 ∨ x = ofT minusT ∨ ∀ w ≠ 0, act x w ≠ w ∧ act x w ≠ -w := by
  intro x hx
  have h := ch1322001n00
  unfold n0C at h
  obtain ⟨-, -, hall⟩ := lstK_spec h
  obtain ⟨n1, -, n3, -⟩ := normC_spec (i := 0) (by norm_num)
  obtain ⟨hv, -, hiff, -⟩ := lst_spec (R := fun i => nR.getD (i - 0) (0, 0, 0, 0)) n1 n3
    (by norm_num) fun i hi => (hall i (Nat.zero_le i) hi).2
  rw [normalizer_D₀] at hx
  obtain ⟨t, ht, rfl⟩ := (hiff x).1 hx
  have he := ch1322001ne0
  unfold noEigC at he
  rw [List.all_eq_true] at he
  have := he t (List.mem_range.2 ht)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with (h1 | h1) | h1
  · left
    rw [h1, ofT_oneT]
  · right; left
    rw [h1]
    rfl
  · right; right
    intro w hw
    exact noEig_spec (hv t ht).2 h1 hw

theorem fixC_eq : ((List.range 81).filter fun v =>
    vecC (toCT p0.1) v == v && vecC (toCT p0.2) v == v) = [0, 3, negV 3] := by
  have h := ch1322001fix0
  unfold fixC at h
  exact beq_iff_eq.1 h

theorem toV_three_ne : toV 3 ≠ 0 := by
  intro h
  have := congrFun h (.inl 1)
  revert this
  decide

theorem fix_P0 {w : Fin 2 ⊕ Fin 2 → ZMod 3}
    (hw : ∀ y ∈ sub2T p0.1 p0.2, act y w = w) : w = 0 ∨ w = toV 3 ∨ w = -toV 3 := by
  obtain ⟨p1, p2, -⟩ := lst_p0
  have h1 := hw (ofT p0.1) (Subgroup.subset_closure (by simp))
  have h2 := hw (ofT p0.2) (Subgroup.subset_closure (by simp))
  have hk : toV (encV w) = w := toV_encV w
  have hv1 : vecC (toCT p0.1) (encV w) = encV w :=
    eq_of_toV_eq (vecC_lt _ _) (encV_lt w) (by rw [← act_ofT p1, hk, h1])
  have hv2 : vecC (toCT p0.2) (encV w) = encV w :=
    eq_of_toV_eq (vecC_lt _ _) (encV_lt w) (by rw [← act_ofT p2, hk, h2])
  have hmem : encV w ∈ (List.range 81).filter
      (fun v => vecC (toCT p0.1) v == v && vecC (toCT p0.2) v == v) :=
    List.mem_filter.2 ⟨List.mem_range.2 (encV_lt w), by simp [hv1, hv2]⟩
  rw [fixC_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  · left
    rw [← hk, h, toV_zero]
  · right; left
    rw [← hk, h]
  · right; right
    rw [← hk, h]
    exact toV_negV 3

theorem P0_fix : ∀ y ∈ sub2T p0.1 p0.2, act y (toV 3) = toV 3 := by
  obtain ⟨p1, p2, -⟩ := lst_p0
  have he : 3 ∈ (List.range 81).filter
      (fun v => vecC (toCT p0.1) v == v && vecC (toCT p0.2) v == v) := by
    rw [fixC_eq]
    simp
  rw [List.mem_filter] at he
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨-, he1, he2⟩ := he
  intro y hy
  have hy' : y ∈ Subgroup.closure ({ofT p0.1, ofT p0.2} : Set G) := hy
  clear hy
  induction hy' using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [act_ofT p1, he1]
    · rw [act_ofT p2, he2]
  | one => exact act_one _
  | mul x z _ _ hx hz => rw [act_mul, hz, hx]
  | inv x _ hx =>
    calc act x⁻¹ (toV 3) = act x⁻¹ (act x (toV 3)) := by rw [hx]
      _ = toV 3 := act_inv_act x _

theorem inf_le (D : Sylow 5 G) (P : Sylow 3 G) :
    Nat.card ↥(normalizer (D : Set G) ⊓ normalizer (P : Set G)) ≤ 2 := by
  obtain ⟨D₀, hD₀⟩ := sylow5
  obtain ⟨P₀, hP₀⟩ := sylow3
  have hm : InG minusT := inG_of_spT okT_minusT (by
    have := sp5C_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have h := ch1322001h30
    unfold h3C at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rwa [h.1.1] at this)
  refine card_inf_le_of (m := ofT minusT) (fun D P x hxD hxP => ?_) D P
  refine mem_inf_of (D₀ := D₀) (P₀ := P₀) (e := toV 3) toV_three_ne (minusT_center hm)
    (fun y hy => P0_fix y (hP₀ ▸ hy)) (fun w hw => fix_P0 fun y hy => hw y (hP₀ ▸ hy))
    (fun x hx => normalizer_D₀_noEig x (hD₀ ▸ hx)) D P hxD hxP

theorem card_member' : ∀ i < 5, Nat.card (Mk i) = memOrd.getD i 0 := by
  intro i hi
  rw [card_mk hi]
  interval_cases i <;> rfl

theorem gfacts : GFacts Mk (fun i => nr.getD i 0) xR where
  card := card_G
  card_member := card_member'
  member_five := mk_five
  exists_rep := fun _ hi y hy hy1 => exists_rep hi y hy hy1
  case_spec := fun _ hi _ hr => case_spec hi hr
  three := three
  four := four
  normD := normD
  normP := normP
  inf_le := inf_le

theorem sp43_facts : Nat.card (Matrix.symplecticGroup (Fin 2) (ZMod 3)) = 51840 ∧
    ∀ W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)), oPPrimeHull 3 W = W → GenProp W :=
  ⟨card_G, fun _ hW => gfacts.genProp hW⟩

end CFSG.KD.Sp43K

end
