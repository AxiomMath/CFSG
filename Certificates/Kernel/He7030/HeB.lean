
module

public import Certificates.Kernel.He7030.YK
public import Certificates.Kernel.He7030.YE3
public import Certificates.Kernel.He7030.YE4
public import Certificates.Kernel.HeDc.Final
public import CFSG.Certificates.Kernel.PtEnumSound
public import CFSG.Quasithin.H13.OverSylowHeBBase
public import CFSG.Quasithin.H13.LocDblHe
public import CFSG.Quasithin.H13.OverSylowHe
public import Certificates.Data.DcHeOverV
public import Certificates.Data.DcSub

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He7030

open CFSG.KC.PtEnum CFSG.KC.E64F CFSG.KC.SLDc CFSG.KD.HeDc
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H13.LocDbl.OverHe (SubO2Prop)
open CFSG.Sporadic.He (J a b)

theorem invW_lt (w : List ℕ) : ∀ l ∈ invW w, l < 2 := by
  intro l hl
  simp only [invW, List.mem_flatMap] at hl
  obtain ⟨x, -, hx⟩ := hl
  cases h : Nat.beq x 0 <;> simp [h] at hx <;> omega

theorem good_we {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good 8330 (tab 8330 (wordElt a b w)).toArray (wordF L w) := by
  have hel : ∀ l < (#[a, b] : Array J).size,
      (#[heTa, heTb] : Array (Array ℕ)).getD l #[] = (tab 8330 ((#[a, b] : Array J).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l
    · exact he_ta.symm
    · exact he_tb.symm
  have e := wordTabA_eq #[a, b] _ hel w (by simpa using hw)
  change Good 8330 (tab 8330 (evalElt #[a, b] w)).toArray (wordF L w)
  rw [← e]
  exact good_word good_ab (by simpa using hw)

theorem base_fix {x : J} (h : ∀ p ∈ base, act 8330 x p = p) : x = 1 :=
  he_base_property x (by rw [base_eq]; exact h)

theorem base_lt : ∀ p ∈ base, p < 8330 := by decide

theorem inv_of_base {x y : J} {f g : ℕ → ℕ} (hx : Good 8330 (tab 8330 x).toArray f)
    (hy : Good 8330 (tab 8330 y).toArray g) (h : invB f g = true) : y = x⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (base_fix fun p hp => ?_)
  have hp' := base_lt p hp
  have hb := List.all_eq_true.1 h p hp
  rw [act_mul _ _ hp', (act_of_good hy hp').1, (act_of_good hx (act_of_good hy hp').2).1]
  exact Nat.eq_of_beq_eq_true hb

@[expose] noncomputable def yL (k : ℕ) : List J := (yW k).map (wordElt a b)

@[expose] noncomputable def mE (k : ℕ) : J := wordElt a b (mW k)

structure Ord (k : ℕ) : Prop where
  lt : ∀ w ∈ yW k, ∀ l ∈ w, l < 2
  mlt : ∀ l ∈ mW k, l < 2
  cube : ∀ w ∈ yW k, ∀ p ∈ base, wordF L w (wordF L w (wordF L w p)) = p
  minv : invB (wordF L (mW k)) (wordF L (invW (mW k))) = true

theorem ord_of {k : ℕ} (h : ordChk k = true) : Ord k := by
  unfold ordChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h5⟩ := h
  exact ⟨h1, h2, fun w hw p hp => Nat.eq_of_beq_eq_true (h3 w hw p hp), h5⟩

theorem getF_YG {k j : ℕ} (hj : j < (yW k).length) :
    getF (YG k) j = wordF L ((yW k)[j]) := by
  simp [getF, YG, List.getD_eq_getElem?_getD, hj]

theorem yL_getD {k j : ℕ} (hj : j < (yW k).length) :
    (yL k).getD j 1 = wordElt a b ((yW k)[j]) := by
  simp [yL, List.getD_eq_getElem?_getD, hj]

theorem enum_ok {k : ℕ} (h : enumChk k = true) :
    rowsOKF 8330 base (YG k) (eT k) (ePar k) (eLab k) (eCl k) = true ∧ (eT k).size = 192 := by
  unfold enumChk at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.2, Nat.eq_of_beq_eq_true h.1⟩

theorem YG_len (k : ℕ) : (YG k).length = (yL k).length := by simp [YG, yL]

theorem YG_act {k : ℕ} (ho : Ord k) :
    ∀ j < (yL k).length, ∀ p < 8330, getF (YG k) j p = act 8330 ((yL k).getD j 1) p := by
  intro j hj p hp
  have hj' : j < (yW k).length := by simpa [yL] using hj
  have hw := ho.lt _ (List.getElem_mem hj')
  rw [getF_YG hj', yL_getD hj', (act_of_good (good_we hw) hp).1]

@[expose] noncomputable def YV (k : ℕ) : Subgroup J := Subgroup.closure {x | x ∈ yL k}

theorem YV_card {k : ℕ} (ho : Ord k) (h : enumChk k = true) : Nat.card (YV k) = 2 ^ 6 * 3 := by
  obtain ⟨hE, hs⟩ := enum_ok h
  rw [YV, card_of_rowsOKF (fun g hg => base_fix hg) (YG_len k) (YG_act ho) hE, hs]
  rfl

theorem yL_cube {k : ℕ} (ho : Ord k) : ∀ y ∈ yL k, y ^ 3 = 1 := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  have hg := good_we (ho.lt w hw)
  refine base_fix fun p hp => ?_
  have hp' := base_lt p hp
  rw [pow_succ, pow_two, act_mul _ _ hp', act_mul _ _ (act_lt _ hp'), (act_of_good hg hp').1,
    (act_of_good hg (act_of_good hg hp').2).1,
    (act_of_good hg (act_of_good hg (act_of_good hg hp').2).2).1]
  exact ho.cube w hw p hp

theorem conj_mem {k : ℕ} (ho : Ord k) (h : enumChk k = true) {v vi y : J} {fv fvi fy : ℕ → ℕ}
    (hv : Good 8330 (tab 8330 v).toArray fv) (hvi : Good 8330 (tab 8330 vi).toArray fvi)
    (hy : Good 8330 (tab 8330 y).toArray fy) (e : vi = v⁻¹)
    (hrow : (eT k).contains (base.map fun q => fv (fy (fvi q))) = true) :
    v * y * v⁻¹ ∈ YV k := by
  obtain ⟨hE, -⟩ := enum_ok h
  refine mem_of_rowsOKF (fun g hg => base_fix hg) (YG_len k) (YG_act ho) hE ?_
  have hrow' := Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hrow)
  convert hrow' using 1
  unfold rt
  refine List.map_congr_left fun q hq => ?_
  have hq' := base_lt q hq
  rw [← e, act_mul _ _ hq', act_mul _ _ (act_lt _ hq'), (act_of_good hvi hq').1,
    (act_of_good hy (act_of_good hvi hq').2).1,
    (act_of_good hv (act_of_good hy (act_of_good hvi hq').2).2).1]

theorem mem_normalizer_of_gens {G : Type} [Group G] [Finite G] {L : List G} {v : G}
    (h : ∀ y ∈ L, v * y * v⁻¹ ∈ Subgroup.closure {x | x ∈ L}) :
    v ∈ Subgroup.normalizer (Subgroup.closure {x | x ∈ L} : Set G) := by
  set H := Subgroup.closure {x | x ∈ L}
  have hle : H.map (MulAut.conj v).toMonoidHom ≤ H := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : H.map (MulAut.conj v).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj v).injective])
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [← heq]
    exact ⟨g, hg, rfl⟩
  · rw [← heq] at hg
    obtain ⟨g', hg', e⟩ := hg
    have : g' = g := by
      simpa [MulAut.conj_apply] using e
    rw [← this]
    exact hg'

theorem mw_k {k : ℕ} (hk : k = 3 ∨ k = 4) : heMwLit[k]! = [mW k] := by
  rcases hk with rfl | rfl <;> (rw [mW, mwJ]; rfl)

theorem Y_k {k : ℕ} (hk : k = 3 ∨ k = 4) :
    heCtxK.Y k = Subgroup.closure {x | x ∈ heSg ++ [mE k]} := by
  change Subgroup.closure {x | x ∈ heSg ++ (heMwLit[k]!).map (wordElt a b)} = _
  rw [mw_k hk]
  rfl

theorem ord_k {k : ℕ} (hk : k = 3 ∨ k = 4) : Ord k := by
  rcases hk with rfl | rfl
  · exact ord_of ord3
  · exact ord_of ord4

theorem enum_k {k : ℕ} (hk : k = 3 ∨ k = 4) : enumChk k = true := by
  rcases hk with rfl | rfl
  · exact enum3
  · exact enum4

theorem norm_k {k : ℕ} (hk : k = 3 ∨ k = 4) :
    ∀ v ∈ VG k, ∀ w ∈ yW k, (eT k).contains (base.map fun q => v.1 (wordF L w (v.2 q))) =
      true := by
  have h : normChk k = true := by
    rcases hk with rfl | rfl
    · exact norm3
    · exact norm4
  unfold normChk at h
  simpa only [List.all_eq_true] using h

theorem lab_k {k : ℕ} (hk : k = 3 ∨ k = 4) :
    ∀ j ∈ lows k, ∀ w ∈ yW k, (Om j).lbl.toList.contains (labF (wordF L w) Δ) = true := by
  have h : labChk k = true := by
    rcases hk with rfl | rfl
    · exact lab3
    · exact lab4
  unfold labChk at h
  simpa only [List.all_eq_true] using h

theorem s_pair {i : ℕ} (hi : i < 4) :
    Good 8330 (tab 8330 (E (heQp.getD i (0, 0)).1)).toArray (L (Nat.add 2 i)) ∧
      Good 8330 (tab 8330 (E (heQp.getD i (0, 0)).2)).toArray (L (Nat.add 6 i)) ∧
      E (heQp.getD i (0, 0)).2 = (E (heQp.getD i (0, 0)).1)⁻¹ := by
  have key : ∀ j j', nodes.getD (Nat.add 2 i) 0 = j → j < heProg.length + 2 →
      nodes.getD (Nat.add 6 i) 0 = j' → j' < heProg.length + 2 →
      Good 8330 (tab 8330 (E j)).toArray (L (Nat.add 2 i)) ∧
        Good 8330 (tab 8330 (E j')).toArray (L (Nat.add 6 i)) ∧ E j' = (E j)⁻¹ :=
    fun j j' e1 h1 e2 h2 => ⟨good_L e1 h1, good_L e2 h2,
      eq_inv_of_maps (good_L e2 h2) (good_L e1 h1) (hinvL i hi)⟩
  interval_cases i
  · exact key 197 256 rfl (by decide) rfl (by decide)
  · exact key 207 262 rfl (by decide) rfl (by decide)
  · exact key 226 263 rfl (by decide) rfl (by decide)
  · exact key 247 266 rfl (by decide) rfl (by decide)

theorem norm_V {k : ℕ} (hk : k = 3 ∨ k = 4) :
    heCtxK.Y k ≤ Subgroup.normalizer (YV k : Set J) := by
  have ho := ord_k hk
  have hn := norm_k hk
  have conj : ∀ (v vi : J) (fv fvi : ℕ → ℕ), (fv, fvi) ∈ VG k →
      Good 8330 (tab 8330 v).toArray fv → Good 8330 (tab 8330 vi).toArray fvi → vi = v⁻¹ →
      v ∈ Subgroup.normalizer (YV k : Set J) := by
    intro v vi fv fvi hmem hv hvi e
    refine mem_normalizer_of_gens fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
    exact conj_mem ho (enum_k hk) hv hvi (good_we (ho.lt w hw)) e (hn _ hmem w hw)
  rw [Y_k hk, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · rw [heSg_eq] at hx
    have hS : ∀ i < 4, E (heQp.getD i (0, 0)).1 ∈ Subgroup.normalizer (YV k : Set J) := by
      intro i hi
      obtain ⟨h1, h2, h3⟩ := s_pair hi
      refine conj _ _ _ _ ?_ h1 h2 h3
      interval_cases i <;> simp [VG]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hS 0 (by decide)
    · exact hS 1 (by decide)
    · exact hS 2 (by decide)
    · exact hS 3 (by decide)
  · exact conj _ _ _ _ (by simp [VG]) (good_we ho.mlt) (good_we (invW_lt _))
      (inv_of_base (good_we ho.mlt) (good_we (invW_lt _)) ho.minv)

theorem gen_mem {k : ℕ} (hk : k = 3 ∨ k = 4) {j : ℕ} (hj : j ∈ lows k) :
    ∀ y ∈ yL k, y ∈ heCtxK.Y j := by
  have ho := ord_k hk
  intro y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  have hj11 : j < 11 := by rcases hk with rfl | rfl <;> simp [lows] at hj <;> omega
  have hc := lab_k hk j hj w hw
  rw [List.contains_iff_mem, Array.mem_toList_iff, Array.mem_iff_getElem] at hc
  obtain ⟨x, hx, e⟩ := hc
  have hJ : j < heCtxK.J := by rw [heK_J]; exact hj11
  have hOm : heCtxK.D.Om[j]! = Om j := by rw [heK_D_Om, Om_get hj11]
  refine (heCtxK.Y_mem_iff hJ _).2 ⟨x, by rw [hOm]; exact hx, ?_⟩
  rw [hOm, getElem!_pos _ x hx, e]
  change ptAct (tab 8330 (wordElt a b w)).toArray heDelta = _
  rw [CFSG.KC.SLOm.ptAct_good (good_we (ho.lt w hw)) delta_lt]
  rfl

theorem subO2_mem {k j : ℕ} (hk : k = 3 ∨ k = 4) (hj : j < 11) (hjl : j ∈ lows k)
    (hjk : k ∈ heIncl[j]!) : SubO2Prop (2 ^ 6 * 3) (heCtxK.Y j) :=
  CFSG.Quasithin.H13.LocDbl.OverHe.SubO2Prop.of_gens
    ((heK_Y_le_iff hj (by rcases hk with rfl | rfl <;> decide)).2 hjk)
    (YV_card (ord_k hk) (enum_k hk)) (yL_cube (ord_k hk)) (norm_V hk) (gen_mem hk hjl)

theorem subO2_of_le {U : Subgroup J} (hSU : heCtxK.S ≤ U) (hU : Nat.card U = 2 ^ 10 * 3 ^ 2) :
    SubO2Prop (2 ^ 6 * 3) U := by
  obtain ⟨j, -, rfl⟩ := heK_complete U hSU
  unfold memberOrTop at hU ⊢
  by_cases h : j < 11
  · rw [if_pos h] at hU ⊢
    rw [heK_member_card j h] at hU
    interval_cases j <;> norm_num at hU
    · exact subO2_mem (Or.inl rfl) (by decide) (by decide) (by decide)
    · exact subO2_mem (Or.inl rfl) (by decide) (by decide) (by decide)
    · exact subO2_mem (Or.inr rfl) (by decide) (by decide) (by decide)
  · rw [if_neg h, Subgroup.card_top, he_card] at hU
    norm_num at hU

theorem heSubO2_JK : ∀ U : Subgroup J, Nat.card U = 2 ^ 10 * 3 ^ 2 → SubO2Prop (2 ^ 6 * 3) U :=
  CFSG.Quasithin.H13.LocDbl.OverHe.SubO2Prop.of_sylow (R := heCtxK.S)
    (by rw [heK_card_S]; norm_num) (by rw [he_card]; norm_num) fun _ hSU hU => subO2_of_le hSU hU

end CFSG.KD.He7030

end
