module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuDcInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.RuK

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLOm
open CFSG.Open (pCoreOf)

open CFSG.KD.RuDc (nodes L C D Om Ot Lm memOK gensInF inclL)

theorem n_eq : ruData.n = 4060 := rfl

theorem slp_get : ∀ (l : List (ℕ × ℕ)) (arr : Array (Array ℕ)) (i : ℕ), i < arr.size →
    (l.foldl slpStepA arr)[i]! = arr[i]!
  | [], _, _, _ => rfl
  | p :: l, arr, i, hi => by
    rw [List.foldl_cons, slp_get l _ i (by simp [slpStepA]; omega)]
    unfold slpStepA
    rw [getElem!_pos (arr.push _) i (by simp; omega), getElem!_pos arr i hi,
      Array.getElem_push_lt hi]

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem slp0 : ruSLP[0]! = ruTa := by
  unfold ruSLP slpTabsA
  rw [slp_get ruProg _ 0 (by simp)]
  rfl

theorem slp1 : ruSLP[1]! = ruTb := by
  unfold ruSLP slpTabsA
  rw [slp_get ruProg _ 1 (by simp)]
  rfl

theorem ruTaL_eq : ruTaL = ruTa := rfl

theorem ruTbL_eq : ruTbL = ruTb := rfl

theorem ruSLPL_eq : ruSLPL = ruSLP := by
  have hp : ruProgL = ruProg := by decide
  unfold ruSLPL ruSLP
  rw [hp, ruTaL_eq, ruTbL_eq]

theorem ru_sTabs : ruSTabsL = [ruSLP[163]!, ruSLP[172]!, ruSLP[185]!] := by
  have hq : ruQpL = ruQp := rfl
  unfold ruSTabsL
  rw [ruSLPL_eq, hq]
  rfl

theorem sTabs_len : ruSTabsL.length = 3 := by
  rw [ru_sTabs]; rfl

section Group

theorem ru_facts : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts

theorem ru_ta : (tab ruData.n (a ruData)).toArray = ruTaL := by
  have : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a ru_facts.toBaseFacts)]
    simp [ruTa]
  rw [ruTaL_eq, this, Array.toArray_toList]

theorem ru_tb : (tab ruData.n (b ruData)).toArray = ruTbL := by
  have : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b ru_facts.toBaseFacts)]
    simp [ruTb]
  rw [ruTbL_eq, this, Array.toArray_toList]

theorem ru_card : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv ru_facts.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  rw [hcard0]; norm_num

theorem ru_cert' : BaseCertS ruData.n ruB
    (slpTabsA (tab ruData.n (a ruData)).toArray (tab ruData.n (b ruData)).toArray ruProg) ruQp
    154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 := by
  rw [ru_ta, ru_tb, ruTaL_eq, ruTbL_eq]
  exact ru_cert

@[expose] noncomputable def ruSg : List (J ruData) :=
  ruQp.map fun p => (slpElts (a ruData) (b ruData) ruProg).getD p.1 1

theorem ruSg_def : ruSg = ruQp.map fun p => (slpElts (a ruData) (b ruData) ruProg).getD p.1 1 := by
  unfold ruSg
  rfl

theorem ru_sGens :
    genTabs ruData.n ruSg = ruSTabsL ∧ Nat.card (Subgroup.closure {x | x ∈ ruSg}) = 2 ^ 14 := by
  have := sGens_of_baseCertS (n := ruData.n) ruB (base_lt ru_facts) (base_property ru_facts)
    (a ruData) (b ruData) ruProg ru_valid ruQp 154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2
    14 ru_cert'
  refine ⟨?_, this.2⟩
  rw [ruSg, this.1, ru_ta, ru_tb]
  rfl

@[irreducible] noncomputable def E (j : ℕ) : J ruData :=
  (slpElts (a ruData) (b ruData) ruProg).getD j 1

theorem ruSg_eq : ruSg = [E 163, E 172, E 185] := by
  simp only [ruSg, ruQp, List.map_cons, List.map_nil, E]

theorem elts_get : ∀ (l : List (ℕ × ℕ)) (arr : Array (J ruData)) (i : ℕ), i < arr.size →
    (l.foldl eltStep arr).getD i 1 = arr.getD i 1
  | [], _, _, _ => rfl
  | p :: l, arr, i, hi => by
    rw [List.foldl_cons, elts_get l _ i (by simp [eltStep]; omega)]
    unfold eltStep
    exact getD_push_lt arr _ 1 hi

theorem E0 : E 0 = a ruData := by
  unfold E slpElts
  rw [elts_get ruProg _ 0 (by simp)]
  rfl

theorem E1 : E 1 = b ruData := by
  unfold E slpElts
  rw [elts_get ruProg _ 1 (by simp)]
  rfl

theorem tab_node {j : ℕ} (hj : j < ruProg.length + 2) :
    (tab ruData.n (E j)).toArray = ruSLP[j]! := by
  have hinv := slp_foldl_inv (n := ruData.n) ruProg #[a ruData, b ruData]
    #[(tab ruData.n (a ruData)).toArray, (tab ruData.n (b ruData)).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using ru_valid)
  have hs : j < (ruProg.foldl slpStepA
      #[(tab ruData.n (a ruData)).toArray, (tab ruData.n (b ruData)).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : ruProg.foldl slpStepA
      #[(tab ruData.n (a ruData)).toArray, (tab ruData.n (b ruData)).toArray] = ruSLP := by
    rw [ru_ta, ru_tb]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

noncomputable def sl : List (J ruData) := [E 163, E 172, E 185, E 198, E 203, E 207]

section Facts

variable (h : RuDcFacts)

include h in
theorem good_L {l : ℕ} (hl : l < 8) :
    Good ruData.n (tab ruData.n (E (nodes.getD l 0))).toArray (C.L l) := by
  rw [tab_node (j := nodes.getD l 0) (by interval_cases l <;> decide), ← ruSLPL_eq]
  exact h.1.2.2.2 l hl

include h in
theorem hL : ∀ l < 2 + C.ns,
    Good ruData.n (tab ruData.n ((a ruData :: b ruData :: sl).getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  have e : (a ruData :: b ruData :: sl).getD l 1 = E (nodes.getD l 0) := by
    interval_cases l
    · exact E0.symm
    · exact E1.symm
    all_goals rfl
  rw [e]
  exact good_L h hl'

theorem act_of_good {x : J ruData} {f : ℕ → ℕ} (hx : Good ruData.n (tab ruData.n x).toArray f)
    {p : ℕ} (hp : p < ruData.n) : act ruData.n x p = f p ∧ f p < ruData.n := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : J ruData} {f g : ℕ → ℕ}
    (hx : Good ruData.n (tab ruData.n x).toArray f) (hy : Good ruData.n (tab ruData.n y).toArray g)
    (hfg : ∀ p < ruData.n, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_property ru_facts
  intro b hb
  have hb' := base_lt ru_facts b hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact hfg b hb'

theorem htake : sl.take 3 = ruSg := by
  rw [ruSg_eq]
  rfl

include h in
theorem hinvL : ∀ i < 3, ∀ p < ruData.n, L (Nat.add 5 i) (L (Nat.add 2 i) p) = p := by
  intro i hi p hp
  have h0 := h.1.2.1
  unfold CFSG.KD.RuDc.invOK at h0
  exact beq_iff_eq.1 (all_range (all_range h0 i hi) p hp)

include h in
theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  have hg : ∀ y ∈ [E 163, E 172, E 185], y ∈ Subgroup.closure {x | x ∈ ruSg} :=
    fun y hy => Subgroup.subset_closure (by rw [ruSg_eq]; exact hy)
  have hm : ∀ i < 3, ∀ j k : ℕ, Nat.add 2 i < 8 → Nat.add 5 i < 8 →
      nodes.getD (Nat.add 2 i) 0 = j → nodes.getD (Nat.add 5 i) 0 = k →
      E j ∈ [E 163, E 172, E 185] → E k ∈ Subgroup.closure {x | x ∈ ruSg} := by
    intro i hi j k h1 h2 e1 e2 hmem
    have g1 := good_L h h1
    have g2 := good_L h h2
    rw [e1] at g1
    rw [e2] at g2
    rw [eq_inv_of_maps g2 g1 (hinvL h i hi)]
    exact Subgroup.inv_mem _ (hg _ hmem)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hm 0 (by decide) 163 198 (by decide) (by decide) rfl rfl (by simp)
  · exact hm 1 (by decide) 172 203 (by decide) (by decide) rfl rfl (by simp)
  · exact hm 2 (by decide) 185 207 (by decide) (by decide) rfl rfl (by simp)

include h in
theorem hsep : ∀ g : J ruData, (∀ p ∈ D.sep, act ruData.n g p = p) → g = 1 := by
  intro g hg
  rw [h.2.1] at hg
  exact base_property ru_facts g hg

include h in
theorem mw_get (j : ℕ) : D.mw.getD j [] = ruMw[j]! := by
  rw [h.1.2.2.1, List.getD_eq_getElem?_getD, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getElem?_toList]
  rfl

theorem mw_size : ruMw.size = 5 := rfl

include h in
theorem dc_facts :
    (∀ g : J ruData, lab ruData.n ptLab ruDelta g = ruDelta ↔
      g ∈ Subgroup.closure {x | x ∈ ruSg}) ∧
    ∀ Z : Subgroup (J ruData), Subgroup.closure {x | x ∈ ruSg} ≤ Z → ∃ j ≤ 5,
      Z = memberOrTop 5 (fun j => Subgroup.closure {x | x ∈ ruSg ++
        (ruMw[j]!).map (wordElt (a ruData) (b ruData))}) j := by
  have h0 := dcCheck_sound (Γ := J ruData) (n := ruData.n) C rfl D (a ruData) (b ruData)
    (closure_ab ruData) sl rfl (hL h) (hS h)
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 14
        rw [htake]; exact ru_sGens.2)
    (by change Nat.card (J ruData) = 8906625 * 2 ^ 14; rw [ru_card, mul_comm]) (hsep h)
    (by decide) h.1.1
  change (∀ g : J ruData, lab ruData.n ptLab ruDelta g = ruDelta ↔
      g ∈ Subgroup.closure {x | x ∈ sl.take 3}) ∧
    ∀ Z : Subgroup (J ruData), Subgroup.closure {x | x ∈ sl.take 3} ≤ Z →
      ∃ j ≤ D.mw.length, Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 3 ++ (D.mw.getD j []).map (wordElt (a ruData) (b ruData))}) j at h0
  rw [htake] at h0
  have hlen : D.mw.length = 5 := by rw [h.1.2.2.1]; rfl
  refine ⟨h0.1, fun Z hZ => ?_⟩
  obtain ⟨j, hj, hZj⟩ := h0.2 Z hZ
  refine ⟨j, by omega, ?_⟩
  rw [hZj, hlen]
  simp only [mw_get h]

end Facts

end Group

theorem labF_lt {f : ℕ → ℕ} (hf : ∀ p < 4060, f p < 4060) {x : List ℕ} (hx : ∀ p ∈ x, p < 4060) :
    ∀ p ∈ labF f x, p < 4060 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (insN_mem hp)
  exact hf q (hx q hq)

theorem om_spec {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good 4060 (letters.getD l #[]) (M l)) {x0 : List ℕ}
    (hx0 : ∀ p ∈ x0, p < 4060) {O : OmegaData (List ℕ)}
    (hO : omOKG (fun l x => labF (M l) x) x0 letters.size O = true) :
    OmegaSpec ptAct letters x0 O ∧ ∀ i < O.lbl.size, ∀ p ∈ O.lbl[i]!, p < 4060 :=
  omOKG_sound (fun x => ∀ p ∈ x, p < 4060) hx0 (fun l hl x hx =>
    ⟨labF_lt (fun p hp => ((hG l hl).2 p hp).2) hx, by
      rw [getElem!_eq_getD']; exact ptAct_good (hG l hl) hx⟩) hO

theorem ot_spec {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good 4060 (letters.getD l #[]) (M l)) {X0 : List (List ℕ)}
    (hX0 : ∀ x ∈ X0, ∀ p ∈ x, p < 4060) {O : OmegaData (List (List ℕ))}
    (hO : omOKG (fun l X => X.map (labF (M l))) X0 letters.size O = true) :
    OmegaSpec (tupAct ptAct) letters X0 O :=
  (omOKG_sound (fun X => ∀ x ∈ X, ∀ p ∈ x, p < 4060) hX0 (fun l hl X hX => by
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact labF_lt (fun p hp => ((hG l hl).2 p hp).2) (hX x hx)
    · unfold tupAct
      refine List.map_congr_left fun x hx => ?_
      rw [getElem!_eq_getD']
      exact ptAct_good (hG l hl) (hX x hx)) hO).1

theorem Om_get {j : ℕ} (hj : j < 5) : ruLatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem Ot_get {j : ℕ} (hj : j < 5) : ruOtK[j]! = Ot j := by
  interval_cases j <;> rfl

theorem mw_lt2B : (ruMw.toList.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) = true :=
  by decide

theorem mw_lt2 {j : ℕ} (hj : j < 5) : ∀ w ∈ ruMw[j]!, ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  have h1 := List.all_eq_true.1 mw_lt2B (ruMw[j]!) (by
    rw [getElem!_pos ruMw j (by rw [mw_size]; exact hj)]
    exact Array.getElem_mem_toList _)
  have := List.all_eq_true.1 (List.all_eq_true.1 h1 w hw) l hl
  simpa using this

theorem mt_get {j : ℕ} (hj : j < 5) :
    ruLatK.mt[j]! = (ruMw[j]!).map (wordTabA #[ruTaL, ruTbL] ruData.n) := by
  change (ruMw.map _)[j]! = (ruMw[j]!).map _
  rw [getElem!_pos _ j (by rw [Array.size_map, mw_size]; exact hj),
    getElem!_pos ruMw j (by rw [mw_size]; exact hj)]
  simp

theorem delta_lt : ∀ p ∈ ruDelta, p < 4060 := by decide

section Members

variable (h : RuDcFacts)

include h in
theorem mems_ok' {j : ℕ} (hj : j < 5) :
    omOKG (fun l x => labF (Lm j l) x) CFSG.KD.RuDc.Δ
        (Nat.add 3 (CFSG.KD.RuDc.J.mw.getD j []).length) (Om j) = true ∧
      omOKG (fun l X => X.map (labF (L (Nat.add 2 l)))) (Om j).lbl.toList 3 (Ot j) = true := by
  have h1 := List.all_eq_true.1 h.2.2.2.2.2.1 j (List.mem_range.2 hj)
  unfold memOK at h1
  rwa [Bool.and_eq_true] at h1

include h in
theorem mwJ (j : ℕ) : CFSG.KD.RuDc.J.mw.getD j [] = ruMw[j]! := mw_get h j

include h in
theorem good_node {l : ℕ} (hl : l < 8) :
    Good ruData.n ruSLP[nodes.getD l 0]! (L l) := by
  rw [← ruSLPL_eq]
  exact h.1.2.2.2 l hl

include h in
theorem good_ab : ∀ l < (#[ruTaL, ruTbL] : Array (Array ℕ)).size,
    Good 4060 ((#[ruTaL, ruTbL] : Array (Array ℕ)).getD l #[]) (L l)
  | 0, _ => by
    have g := good_node h (l := 0) (by decide)
    change Good 4060 ruSLP[0]! (L 0) at g
    rw [slp0] at g
    exact g
  | 1, _ => by
    have g := good_node h (l := 1) (by decide)
    change Good 4060 ruSLP[1]! (L 1) at g
    rw [slp1] at g
    exact g
  | _ + 2, hl => absurd hl (by simp)

include h in
theorem good_s {l : ℕ} (hl : l < 3) : Good 4060 (ruSTabsL.toArray.getD l #[]) (L (Nat.add 2 l)) := by
  rw [ru_sTabs]
  interval_cases l
  · exact good_node h (l := 2) (by decide)
  · exact good_node h (l := 3) (by decide)
  · exact good_node h (l := 4) (by decide)

include h in
theorem msize {j : ℕ} (hj : j < 5) :
    (ruLatK.sTabs ++ ruLatK.mt[j]!).toArray.size =
      Nat.add 3 (CFSG.KD.RuDc.J.mw.getD j []).length := by
  rw [mt_get hj, mwJ h]
  simp [ruLatK, sTabs_len]

include h in
theorem good_m {j : ℕ} (hj : j < 5) :
    ∀ l < (ruLatK.sTabs ++ ruLatK.mt[j]!).toArray.size,
      Good 4060 ((ruLatK.sTabs ++ ruLatK.mt[j]!).toArray.getD l #[]) (Lm j l) := by
  intro l hl
  have hs : ruLatK.sTabs = ruSTabsL := rfl
  rw [hs, mt_get hj] at hl ⊢
  simp only [List.size_toArray, List.length_append, List.length_map, sTabs_len] at hl
  by_cases h3 : l < 3
  · have e : (ruSTabsL ++ (ruMw[j]!).map (wordTabA #[ruTaL, ruTbL] ruData.n)).toArray.getD l #[] =
        ruSTabsL.toArray.getD l #[] := by
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left (show l < ruSTabsL.length by
        rw [sTabs_len]; exact h3), sTabs_len, h3]
    rw [e]
    have e2 : Lm j l = L (Nat.add 2 l) := by
      have hb : Nat.blt l 3 = true := by simpa using h3
      unfold Lm
      rw [hb]
      rfl
    rw [e2]
    exact good_s h h3
  · obtain ⟨i, rfl⟩ : ∃ i, l = 3 + i := ⟨l - 3, by omega⟩
    have hi : i < (ruMw[j]!).length := by omega
    have e : (ruSTabsL ++ (ruMw[j]!).map (wordTabA #[ruTaL, ruTbL] ruData.n)).toArray.getD
        (3 + i) #[] = wordTabA #[ruTaL, ruTbL] ruData.n ((ruMw[j]!).getD i []) := by
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, sTabs_len, hi,
        List.getD_eq_getElem?_getD]
    rw [e]
    have e2 : Lm j (3 + i) = wordF L ((ruMw[j]!).getD i []) := by
      have hb : Nat.blt (3 + i) 3 = false := by
        cases hc : Nat.blt (3 + i) 3
        · rfl
        · exact absurd (Nat.blt_eq.mp hc) (by omega)
      have hs3 : Nat.sub (3 + i) 3 = i := by change 3 + i - 3 = i; omega
      unfold Lm
      rw [hb]
      change wordF L ((CFSG.KD.RuDc.J.mw.getD j []).getD (Nat.sub (3 + i) 3) []) = _
      rw [mwJ h, hs3]
    rw [e2]
    have hmem : (ruMw[j]!).getD i [] ∈ ruMw[j]! := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact good_word (good_ab h) (fun l hl => by simpa using mw_lt2 hj _ hmem l hl)

include h in
theorem ruK_membersOK : MembersOK ptAct ruData.n ruTaL ruTbL ruDelta ruLatK := by
  refine ⟨by rw [show ruLatK.mw = ruMw from rfl, mw_size]; decide, by decide, by simp [ruLatK],
    rfl, fun j hj => ?_⟩
  have hj' : j < 5 := hj
  refine ⟨mw_lt2 hj', ?_, ?_⟩
  · exact mt_get hj'
  · rw [Om_get hj']
    have h1 := (mems_ok' h hj').1
    rw [← msize h hj'] at h1
    exact (om_spec (good_m h hj') delta_lt h1).1

include h in
theorem ruK_o2OK : O2OK ptAct ruLatK ruOtK := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < 5 := hj
  have h1 := mems_ok' h hj'
  have hsp := om_spec (good_m h hj') delta_lt (by rw [msize h hj']; exact h1.1)
  have hodd : (Om j).lbl.size % 2 = 1 := by interval_cases j <;> rfl
  refine ⟨by rw [Om_get hj']; exact hodd, ?_⟩
  rw [Om_get hj', Ot_get hj']
  have hlt : ∀ x ∈ (Om j).lbl.toList, ∀ p ∈ x, p < 4060 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < (Om j).lbl.size := by simpa using hi
    have : (Om j).lbl.toList[i] = (Om j).lbl[i]! := by
      rw [getElem!_pos _ i hi']; simp
    rw [this]
    exact hsp.2 i hi'
  have hG : ∀ l < ruLatK.sTabs.toArray.size,
      Good 4060 (ruLatK.sTabs.toArray.getD l #[]) (L (Nat.add 2 l)) := fun l hl =>
    good_s h (by simpa [ruLatK, sTabs_len] using hl)
  have hsz : ruLatK.sTabs.toArray.size = 3 := by simp [ruLatK, sTabs_len]
  exact ot_spec hG hlt (by rw [hsz]; exact h1.2)

end Members

theorem incl_get {j : ℕ} (hj : j < 5) : ruIncl[j]! = inclL.getD j [] := by
  interval_cases j <;> rfl

variable (h : RuDcFacts)

include h in
theorem gensIn_iff {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) :
    GensIn ptAct ruDelta ruLatK j jj ↔ gensInF j jj = true := by
  have hmt : ruLatK.mt[j]! = (ruMw[j]!).map (wordTabA #[ruTaL, ruTbL] ruData.n) :=
    mt_get hj
  have hlab : ∀ w ∈ ruMw[j]!, ptAct (wordTabA #[ruTaL, ruTbL] ruData.n w) ruDelta =
      labF (wordF L w) CFSG.KD.RuDc.Δ := fun w hw =>
    ptAct_good (good_word (good_ab h) (fun l hl => by simpa using mw_lt2 hj w hw l hl)) delta_lt
  unfold GensIn gensInF
  rw [hmt, Om_get hjj, mwJ h, List.all_eq_true]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun w hw => ?_
  rw [hlab w hw, List.contains_iff_mem, Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [← e, getElem!_pos _ x hx]⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [getElem!_pos _ x hx, e]⟩

include h in
theorem incl_iff {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) :
    GensIn ptAct ruDelta ruLatK j jj ↔ jj ∈ ruIncl[j]! := by
  rw [gensIn_iff h hj hjj, incl_get hj]
  have hinc := h.2.2.2.2.2.2.2
  unfold CFSG.KD.RuDc.inclOK at hinc
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hinc j (List.mem_range.2 hj)) jj
    (List.mem_range.2 hjj)
  rw [beq_iff_eq] at h1
  rw [h1, List.contains_iff_mem]

end CFSG.QuasithinUnique.Ch1.SporLat.RuK

end
