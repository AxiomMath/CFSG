module

public import Certificates.Kernel.HeDc.Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HeDc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLOm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem labF_lt {f : ℕ → ℕ} (hf : ∀ p < 8330, f p < 8330) {x : List ℕ} (hx : ∀ p ∈ x, p < 8330) :
    ∀ p ∈ labF f x, p < 8330 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (insN_mem hp)
  exact hf q (hx q hq)

theorem om_spec {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good 8330 (letters.getD l #[]) (M l)) {x0 : List ℕ}
    (hx0 : ∀ p ∈ x0, p < 8330) {O : OmegaData (List ℕ)}
    (h : omOKG (fun l x => labF (M l) x) x0 letters.size O = true) :
    OmegaSpec ptAct letters x0 O ∧ ∀ i < O.lbl.size, ∀ p ∈ O.lbl[i]!, p < 8330 :=
  omOKG_sound (fun x => ∀ p ∈ x, p < 8330) hx0 (fun l hl x hx =>
    ⟨labF_lt (fun p hp => ((hG l hl).2 p hp).2) hx, by
      rw [getElem!_eq_getD']; exact ptAct_good (hG l hl) hx⟩) h

theorem ot_spec {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good 8330 (letters.getD l #[]) (M l)) {X0 : List (List ℕ)}
    (hX0 : ∀ x ∈ X0, ∀ p ∈ x, p < 8330) {O : OmegaData (List (List ℕ))}
    (h : omOKG (fun l X => X.map (labF (M l))) X0 letters.size O = true) :
    OmegaSpec (tupAct ptAct) letters X0 O :=
  (omOKG_sound (fun X => ∀ x ∈ X, ∀ p ∈ x, p < 8330) hX0 (fun l hl X hX => by
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact labF_lt (fun p hp => ((hG l hl).2 p hp).2) (hX x hx)
    · unfold tupAct
      refine List.map_congr_left fun x hx => ?_
      rw [getElem!_eq_getD']
      exact ptAct_good (hG l hl) (hX x hx)) h).1

@[expose] noncomputable def heLatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := heSTabsC
  mw := heMwLit
  mt := heMwLit.map fun ws => ws.map (wordTabA #[heTa, heTb] 8330)
  Om := #[Om 0, Om 1, Om 2, Om 3, Om 4, Om 5, Om 6, Om 7, Om 8, Om 9, Om 10]
  atoms := #[]
  joins := []

@[expose] noncomputable def heOtK : Array (OmegaData (List (List ℕ))) :=
  #[Ot 0, Ot 1, Ot 2, Ot 3, Ot 4, Ot 5, Ot 6, Ot 7, Ot 8, Ot 9, Ot 10]

theorem Om_get {j : ℕ} (hj : j < 11) : heLatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem Ot_get {j : ℕ} (hj : j < 11) : heOtK[j]! = Ot j := by
  interval_cases j <;> rfl

theorem mw_size : heMwLit.size = 11 := rfl

theorem mw_lt2B : (heMwLit.toList.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) = true :=
  by quickRfl

theorem mw_lt2 {j : ℕ} (hj : j < 11) : ∀ w ∈ heMwLit[j]!, ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  have h1 := List.all_eq_true.1 mw_lt2B (heMwLit[j]!) (by
    rw [getElem!_pos heMwLit j (by rw [mw_size]; exact hj)]
    exact Array.getElem_mem_toList _)
  have := List.all_eq_true.1 (List.all_eq_true.1 h1 w hw) l hl
  simpa using this

theorem mems_ok {j : ℕ} (hj : j < 11) : memOK j = true :=
  List.all_eq_true.1 mems j (List.mem_range.2 hj)

theorem mems_ok' {j : ℕ} (hj : j < 11) :
    omOKG (fun l x => labF (Lm j l) x) Δ (Nat.add 4 (J.mw.getD j []).length) (Om j) = true ∧
      omOKG (fun l X => X.map (labF (L (Nat.add 2 l)))) (Om j).lbl.toList 4 (Ot j) = true := by
  have h := mems_ok hj
  unfold memOK at h
  rwa [Bool.and_eq_true] at h

theorem mt_get {j : ℕ} (hj : j < 11) :
    heLatK.mt[j]! = (heMwLit[j]!).map (wordTabA #[heTa, heTb] 8330) := by
  change (heMwLit.map _)[j]! = (heMwLit[j]!).map _
  rw [getElem!_pos _ j (by rw [Array.size_map, mw_size]; exact hj),
    getElem!_pos heMwLit j (by rw [mw_size]; exact hj)]
  simp


theorem mwJ (j : ℕ) : J.mw.getD j [] = heMwLit[j]! := mw_get j

theorem good_ab : ∀ l < (#[heTa, heTb] : Array (Array ℕ)).size,
    Good 8330 ((#[heTa, heTb] : Array (Array ℕ)).getD l #[]) (L l)
  | 0, _ => good_a
  | 1, _ => good_b
  | _ + 2, h => absurd h (by simp)

theorem good_s {l : ℕ} (hl : l < 4) : Good 8330 (heSTabsC.toArray.getD l #[]) (L (Nat.add 2 l)) := by
  rw [CFSG.KD.E68S4215.he_sTabs]
  interval_cases l
  · exact CFSG.KD.E68S4215.good_he (j := 197) (by decide)
  · exact CFSG.KD.E68S4215.good_he (j := 207) (by decide)
  · exact CFSG.KD.E68S4215.good_he (j := 226) (by decide)
  · exact CFSG.KD.E68S4215.good_he (j := 247) (by decide)

theorem sTabs_len : heSTabsC.length = 4 := by
  rw [CFSG.KD.E68S4215.he_sTabs]; rfl

theorem msize {j : ℕ} (hj : j < 11) :
    (heLatK.sTabs ++ heLatK.mt[j]!).toArray.size = Nat.add 4 (J.mw.getD j []).length := by
  rw [mt_get hj, mwJ]
  simp [heLatK, sTabs_len]

theorem good_m {j : ℕ} (hj : j < 11) :
    ∀ l < (heLatK.sTabs ++ heLatK.mt[j]!).toArray.size,
      Good 8330 ((heLatK.sTabs ++ heLatK.mt[j]!).toArray.getD l #[]) (Lm j l) := by
  intro l hl
  have hs : heLatK.sTabs = heSTabsC := rfl
  rw [hs, mt_get hj] at hl ⊢
  simp only [List.size_toArray, List.length_append, List.length_map, sTabs_len] at hl
  by_cases h4 : l < 4
  · have e : (heSTabsC ++ (heMwLit[j]!).map (wordTabA #[heTa, heTb] 8330)).toArray.getD l #[] =
        heSTabsC.toArray.getD l #[] := by
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left (show l < heSTabsC.length by
        rw [sTabs_len]; exact h4), sTabs_len, h4]
    rw [e]
    have e2 : Lm j l = L (Nat.add 2 l) := by
      have hb : Nat.blt l 4 = true := by simpa using h4
      unfold Lm
      rw [hb]
      rfl
    rw [e2]
    exact good_s h4
  · obtain ⟨i, rfl⟩ : ∃ i, l = 4 + i := ⟨l - 4, by omega⟩
    have hi : i < (heMwLit[j]!).length := by omega
    have e : (heSTabsC ++ (heMwLit[j]!).map (wordTabA #[heTa, heTb] 8330)).toArray.getD (4 + i) #[] =
        wordTabA #[heTa, heTb] 8330 ((heMwLit[j]!).getD i []) := by
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, sTabs_len, hi,
        List.getD_eq_getElem?_getD]
    rw [e]
    have e2 : Lm j (4 + i) = wordF L ((heMwLit[j]!).getD i []) := by
      have hb : Nat.blt (4 + i) 4 = false := by
        cases h : Nat.blt (4 + i) 4
        · rfl
        · exact absurd (Nat.blt_eq.mp h) (by omega)
      have hs4 : Nat.sub (4 + i) 4 = i := by change 4 + i - 4 = i; omega
      unfold Lm
      rw [hb]
      change wordF L ((J.mw.getD j []).getD (Nat.sub (4 + i) 4) []) = _
      rw [mwJ, hs4]
    rw [e2]
    have hmem : (heMwLit[j]!).getD i [] ∈ heMwLit[j]! := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact good_word good_ab (fun l hl => by simpa using mw_lt2 hj _ hmem l hl)

theorem delta_lt : ∀ p ∈ heDelta, p < 8330 := by decide

theorem heK_membersOK : MembersOK ptAct 8330 heTa heTb heDelta heLatK := by
  refine ⟨by rw [show heLatK.mw = heMwLit from rfl, mw_size]; decide, by decide, by simp [heLatK],
    rfl, fun j hj => ?_⟩
  have hj' : j < 11 := hj
  refine ⟨mw_lt2 hj', ?_, ?_⟩
  · exact mt_get hj'
  · rw [Om_get hj']
    have h := (mems_ok' hj').1
    rw [← msize hj'] at h
    exact (om_spec (good_m hj') delta_lt h).1

theorem heK_o2OK : O2OK ptAct heLatK heOtK := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < 11 := hj
  have h := mems_ok' hj'
  have hsp := om_spec (good_m hj') delta_lt (by rw [msize hj']; exact h.1)
  have hodd : (Om j).lbl.size % 2 = 1 := by interval_cases j <;> rfl
  refine ⟨by rw [Om_get hj']; exact hodd, ?_⟩
  rw [Om_get hj', Ot_get hj']
  have hlt : ∀ x ∈ (Om j).lbl.toList, ∀ p ∈ x, p < 8330 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < (Om j).lbl.size := by simpa using hi
    have : (Om j).lbl.toList[i] = (Om j).lbl[i]! := by
      rw [getElem!_pos _ i hi']; simp
    rw [this]
    exact hsp.2 i hi'
  have hG : ∀ l < heLatK.sTabs.toArray.size,
      Good 8330 (heLatK.sTabs.toArray.getD l #[]) (L (Nat.add 2 l)) := fun l hl =>
    good_s (by simpa [heLatK, sTabs_len] using hl)
  have hsz : heLatK.sTabs.toArray.size = 4 := by simp [heLatK, sTabs_len]
  exact ot_spec hG hlt (by rw [hsz]; exact h.2)

theorem heK_delta_valid : PtValid 8330 heDelta := by decide

@[expose] noncomputable def heCtxK : LatCtx CFSG.Sporadic.He.J 8330 (List ℕ) :=
  LatCtx.ofFacts ptLab (PtValid 8330) ptLab_lawful heDelta heK_delta_valid CFSG.Sporadic.He.a
    CFSG.Sporadic.He.b heTa heTb he_ta he_tb CFSG.Sporadic.He.closure_ab heLatK heSg 10
    he_sGens.1 he_sGens.2 3935925 (by rw [he_card, mul_comm]) heK_membersOK dc_facts.1
    (fun Z hZ => by
      obtain ⟨j, hj, e⟩ := dc_facts.2 Z hZ
      exact ⟨j, by rw [show heLatK.mw = heMwLit from rfl, mw_size]; exact hj, e⟩)

theorem heK_D_Om : heCtxK.D.Om = heLatK.Om := rfl

theorem heK_D_mw : heCtxK.D.mw = heMwLit := rfl

theorem heK_orbit_card : heCtxK.D.O.lbl.size = 3935925 := LatCtx.ofFacts_O_size ..

theorem heK_J : heCtxK.J = 11 := by
  unfold LatCtx.J
  rw [heK_D_mw, mw_size]

theorem heK_complete : ∀ Z : Subgroup CFSG.Sporadic.He.J, heCtxK.S ≤ Z →
    ∃ j ≤ 11, Z = memberOrTop 11 heCtxK.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := heCtxK.complete Z hZ
  rw [heK_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

theorem heK_card_S : Nat.card heCtxK.S = 1024 := by
  rw [heCtxK.S_card]; rfl

theorem heK_Om_size (j : ℕ) (hj : j < 11) :
    heCtxK.D.Om[j]!.lbl.size = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! := by
  rw [heK_D_Om, Om_get hj]
  interval_cases j <;> rfl

theorem heK_Ot_size (j : ℕ) (hj : j < 11) :
    heOtK[j]!.lbl.size = #[1, 2, 4, 16, 16, 4, 2, 8, 2, 4, 2][j]! := by
  rw [Ot_get hj]
  interval_cases j <;> rfl

theorem heK_member_card (j : ℕ) (hj : j < 11) :
    Nat.card (heCtxK.Y j) = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024 := by
  have h1 : j < heCtxK.J := by rw [heK_J]; exact hj
  rw [heCtxK.Y_card h1, heK_Om_size j hj]
  rfl

theorem gensIn_iff {j jj : ℕ} (hj : j < 11) (hjj : jj < 11) :
    GensIn heCtxK.A.act heCtxK.Δ heCtxK.D j jj ↔ gensInF j jj = true := by
  change GensIn ptAct heDelta heCtxK.D j jj ↔ _
  have hmt : heCtxK.D.mt[j]! = (heMwLit[j]!).map (wordTabA #[heTa, heTb] 8330) := mt_get hj
  have hlab : ∀ w ∈ heMwLit[j]!, ptAct (wordTabA #[heTa, heTb] 8330 w) heDelta =
      labF (wordF L w) Δ := fun w hw =>
    ptAct_good (good_word good_ab (fun l hl => by simpa using mw_lt2 hj w hw l hl)) delta_lt
  unfold GensIn gensInF
  rw [hmt, heK_D_Om, Om_get hjj, mwJ, List.all_eq_true]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun w hw => ?_
  rw [hlab w hw, List.contains_iff_mem, Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [← e, getElem!_pos _ x hx]⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [getElem!_pos _ x hx, e]⟩

theorem incl_get {j : ℕ} (hj : j < 11) : heIncl[j]! = inclL.getD j [] := by
  interval_cases j <;> rfl

theorem heK_Y_le_iff {j jj : ℕ} (hj : j < 11) (hjj : jj < 11) :
    heCtxK.Y j ≤ heCtxK.Y jj ↔ jj ∈ heIncl[j]! := by
  rw [heCtxK.Y_le_iff (by rw [heK_J]; exact hj) (by rw [heK_J]; exact hjj), gensIn_iff hj hjj,
    incl_get hj]
  have h := List.all_eq_true.1 (List.all_eq_true.1 incl j (List.mem_range.2 hj)) jj
    (List.mem_range.2 hjj)
  rw [beq_iff_eq] at h
  rw [h, List.contains_iff_mem]

def heMemsK : List Mem :=
  [⟨1024, 1024, 1024⟩, ⟨3072, 512, 3072⟩, ⟨9216, 256, 9216⟩, ⟨138240, 64, 138240⟩,
    ⟨138240, 64, 138240⟩, ⟨9216, 256, 9216⟩, ⟨3072, 512, 3072⟩, ⟨21504, 128, 21504⟩,
    ⟨3072, 512, 3072⟩, ⟨9216, 256, 9216⟩, ⟨3072, 512, 3072⟩]

theorem heK_rows_default : (List.range 11).map (defaultRow 10 heCtxK.D heOtK) = heMemsK := by
  have h : (List.range 11).map (defaultRow 10 heCtxK.D heOtK) =
      (List.range 11).map fun j => (⟨#[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 2 ^ 10,
        2 ^ 10 / #[1, 2, 4, 16, 16, 4, 2, 8, 2, 4, 2][j]!,
        #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 2 ^ 10⟩ : Mem) := by
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [defaultRow, heK_Om_size j hj', heK_Ot_size j hj']
  rw [h]
  rfl

theorem heK_row (j : ℕ) (hj : j < 11) : ∃ m ∈ heMemsK, MemStmt (heCtxK.Y j) m := by
  refine heCtxK.rows_of_default (Ot := heOtK) heK_o2OK heMemsK ?_ j (by rw [heK_J]; exact hj)
  rw [heK_J]
  exact heK_rows_default

theorem heK_S_index : heCtxK.S.index = 3935925 := by
  have h1 := Subgroup.card_mul_index heCtxK.S
  rw [heK_card_S, he_card] at h1
  omega

theorem heK_S_sylow : IsSylowTwoOf heCtxK.S ⊤ := by
  refine CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨heCtxK.S_isPGroup, ?_⟩
  rw [heK_S_index]
  norm_num

open CFSG.Blueprint.NativeSporadic in
theorem heK_overgroups {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Carrier .He))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ heMemsK, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* CFSG.Sporadic.He.J) := ⟨e.trans CFSG.Sporadic.He.heEquivJ⟩
  exact overgroups_of_lattice heCtxK.S heK_S_sylow 11 heCtxK.Y heMemsK heK_complete
    (fun j hj => heK_row j hj) hX' hT hTY

end CFSG.KD.HeDc

end
