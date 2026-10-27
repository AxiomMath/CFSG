module

public import Certificates.Kernel.R148Dc.M22CBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Dc
public import CFSG.RankThree.PartTwo.KFacts.KP4Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.R148Dc.M22C

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m22a m22b card_M22)
open CFSG.RankThree.PartTwo.KFacts.KP4
open CFSG.RankThree.PartTwo.Sec14.Ronan148B.M22 (sg closure_sg card_P0_sup_V)

@[expose] def tl (σ : Equiv.Perm (Fin 22)) : List ℕ := (List.finRange 22).map fun i => (σ i).val

@[expose] noncomputable def labIn (j : ℕ) (t : List ℕ) : Bool :=
  (List.range (Om j).lbl.size).any fun i => (Om j).lbl[i]! == labF (pairF 22 (tabF t)) J.delta

@[expose] def szL : List ℕ := [1, 70, 70, 160, 16, 4, 8, 2]

theorem szK : ((List.range 8).map (fun j => (Om j).lbl.size) == szL) = true := by
  quickRfl

theorem labK : (labIn 1 (tl (vA 2)) && labIn 1 (tl (vB 2)) && labIn 2 (tl (vA 3)) &&
    labIn 2 (tl (vB 3))) = true := by
  quickRfl

theorem mwK : (J.mw.length == 8 && J.mw.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) =
    true := by
  quickRfl

theorem deltaV : PtValid (22 * 22) J.delta := by decide +kernel

local instance pairInst : MulAction G22 (Fin (22 * 22)) := pairAction G22 22

theorem forall₂_getD {R : G22 → List ℕ → Prop} {gs : List G22} {ws : List (List ℕ)}
    (h : List.Forall₂ R gs ws) :
    gs.length = ws.length ∧ ∀ i < gs.length, R (gs.getD i 1) (ws.getD i []) := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    refine ⟨by simp [ih.1], fun i hi => ?_⟩
    rcases i with _ | i
    · exact hr
    · simpa using ih.2 i (by simpa using hi)

theorem member_spec {S : Subgroup G22}
    (hstab : ∀ g : G22, lab (22 * 22) ptLab J.delta g = J.delta ↔ g ∈ S) {gs : List G22}
    {ws : List (List ℕ)}
    (hg : List.Forall₂ (fun g w => Good (22 * 22) (tab (22 * 22) g).toArray (wordF L w)) gs ws)
    (hS : S ≤ Subgroup.closure {g | g ∈ gs}) {O : OmegaData (List ℕ)}
    (hO : omOKG (fun l x => labF (wordF L (ws.getD l [])) x) J.delta ws.length O = true) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = O.lbl.size * Nat.card S ∧
      ∀ g : G22, g ∈ Subgroup.closure {g | g ∈ gs} ↔
        ∃ i < O.lbl.size, lab (22 * 22) ptLab J.delta g = O.lbl[i]! := by
  obtain ⟨hlen, hgi⟩ := forall₂_getD hg
  have hsz : (gs.toArray.map fun g => (tab (22 * 22) g).toArray).size = ws.length := by
    simp [hlen]
  have hget : ∀ l < (gs.toArray.map fun g => (tab (22 * 22) g).toArray).size,
      (gs.toArray.map fun g => (tab (22 * 22) g).toArray).getD l #[] =
        (tab (22 * 22) (gs.getD l 1)).toArray := by
    intro l hl
    have hl' : l < gs.length := by simpa using hl
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_eq_getElem hl', List.getD_eq_getElem _ _ hl']
    rfl
  have hG : ∀ l < (gs.toArray.map fun g => (tab (22 * 22) g).toArray).size,
      Good (22 * 22) ((gs.toArray.map fun g => (tab (22 * 22) g).toArray).getD l #[])
        (wordF L (ws.getD l [])) := fun l hl => by
    rw [hget l hl]
    exact hgi l (by simpa using hl)
  have hO' : OmegaSpec ptAct (gs.toArray.map fun g => (tab (22 * 22) g).toArray) J.delta O :=
    J3K.om_spec (M := fun l => wordF L (ws.getD l [])) hG deltaV.2 (by rw [hsz]; exact hO)
  have hstab' : stab (ptLab_lawful (Γ := G22) (n := 22 * 22)) deltaV = S := by
    ext g
    exact hstab g
  have hel : ∀ l < (gs.toArray.map fun g => (tab (22 * 22) g).toArray).size,
      (gs.toArray.map fun g => (tab (22 * 22) g).toArray)[l]! =
        (tab (22 * 22) (gs.toArray.getD l 1)).toArray := fun l hl => by
    rw [CFSG.KC.SLOm.getElem!_eq_getD', hget l hl, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  have hS' : stab (ptLab_lawful (Γ := G22) (n := 22 * 22)) deltaV ≤
      Subgroup.closure {g | g ∈ gs} := by
    rw [hstab']; exact hS
  have hc := OmegaSpec.card_eq ptLab_lawful deltaV gs.toArray (by simp) hel hO'
    (H := Subgroup.closure {g | g ∈ gs}) (by rw [List.toList_toArray]) hS'
  refine ⟨by rw [hc, hstab'], fun g => ?_⟩
  exact OmegaSpec.mem_iff ptLab_lawful deltaV gs.toArray (by simp) hel hO'
    (H := Subgroup.closure {g | g ∈ gs}) (by rw [List.toList_toArray]) hS' g

theorem hL' {l : ℕ} (hl : l < 10) :
    Good (22 * 22) (tab (22 * 22) ((m22a :: m22b :: sl).getD l 1)).toArray (L l) :=
  hL l hl

theorem good_wordElt {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good (22 * 22) (tab (22 * 22) (wordElt m22a m22b w)).toArray (wordF L w) := by
  have hel : ∀ l < (#[m22a, m22b] : Array G22).size,
      (#[(tab (22 * 22) m22a).toArray, (tab (22 * 22) m22b).toArray] : Array (Array ℕ)).getD l #[] =
        (tab (22 * 22) ((#[m22a, m22b] : Array G22).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l <;> rfl
  have e := wordTabA_eq #[m22a, m22b] _ hel w (by simpa using hw)
  change Good (22 * 22) (tab (22 * 22) (evalElt #[m22a, m22b] w)).toArray (wordF L w)
  rw [← e]
  refine good_word (fun l hl => ?_) (by simpa using hw)
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · exact hL' (l := 0) (by norm_num)
  · exact hL' (l := 1) (by norm_num)

theorem mw_lt {j : ℕ} : ∀ w ∈ J.mw.getD j [], ∀ l ∈ w, l < 2 := by
  have h := mwK
  rw [Bool.and_eq_true] at h
  intro w hw l hl
  by_cases hj : j < J.mw.length
  · rw [List.getD_eq_getElem _ _ hj] at hw
    exact Nat.blt_eq.mp (List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h.2 _
      (List.getElem_mem hj)) w hw) l hl)
  · rw [List.getD_eq_default _ _ (by omega)] at hw
    simp at hw

theorem mw_len : J.mw.length = 8 := by
  have h := mwK
  rw [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem gensF (j : ℕ) : List.Forall₂ (fun g w => Good (22 * 22) (tab (22 * 22) g).toArray (wordF L w))
    (sg ++ (J.mw.getD j []).map (wordElt m22a m22b)) (mE j) := by
  refine fa_append ?_ ?_
  · exact .cons (hL' (l := 2) (by norm_num)) (.cons (hL' (l := 3) (by norm_num))
      (.cons (hL' (l := 4) (by norm_num)) (.cons (hL' (l := 5) (by norm_num)) .nil)))
  · have key : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 2) →
        List.Forall₂ (fun g w => Good (22 * 22) (tab (22 * 22) g).toArray (wordF L w))
          (ws.map (wordElt m22a m22b)) ws := by
      intro ws hws
      induction ws with
      | nil => exact .nil
      | cons w ws ih =>
        exact .cons (good_wordElt (hws w List.mem_cons_self))
          (ih fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    exact key _ mw_lt

@[expose] noncomputable def Y (j : ℕ) : Subgroup G22 :=
  Subgroup.closure {x | x ∈ sg ++ (J.mw.getD j []).map (wordElt m22a m22b)}

theorem sg_le_Y (j : ℕ) : P0 ⊔ V 0 ≤ Y j := by
  rw [← closure_sg]
  exact Subgroup.closure_mono fun x hx => List.mem_append_left _ hx

theorem Y_spec {j : ℕ} (hj : j < 8) :
    Nat.card (Y j) = (Om j).lbl.size * Nat.card (P0 ⊔ V 0 : Subgroup G22) ∧
      ∀ g : G22, g ∈ Y j ↔ ∃ i < (Om j).lbl.size, lab (22 * 22) ptLab J.delta g = (Om j).lbl[i]! :=
  member_spec (S := P0 ⊔ V 0) (fun g => by rw [← closure_sg]; exact m22c_stab g) (gensF j)
    (by rw [← closure_sg]; exact Subgroup.closure_mono fun x hx => List.mem_append_left _ hx)
    (List.all_eq_true.1 mems j (List.mem_range.2 hj))

theorem sz_eq {j : ℕ} (hj : j < 8) : (Om j).lbl.size = szL.getD j 0 := by
  rw [← eq_of_beq szK, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getElem_range]

theorem card_Y {j : ℕ} (hj : j < 8) : Nat.card (Y j) = szL.getD j 0 * 36 := by
  rw [(Y_spec hj).1, card_P0_sup_V, sz_eq hj]

theorem mem_Y_of_labIn {j : ℕ} (hj : j < 8) {g : G22} (h : labIn j (tab 22 g) = true) :
    g ∈ Y j := by
  rw [(Y_spec hj).2]
  obtain ⟨i, hi, he⟩ := List.any_eq_true.1 h
  refine ⟨i, List.mem_range.1 hi, ?_⟩
  have hgood : Good (22 * 22) (tab (22 * 22) g).toArray (pairF 22 (tabF (tab 22 g))) :=
    good_pair (good_tabF rfl ⟨by simp [tab], fun p hp => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
      exact (g • x).isLt⟩)
  change ptAct (tab (22 * 22) g).toArray J.delta = _
  rw [CFSG.KC.SLOm.ptAct_good hgood deltaV.2, eq_of_beq he]
  rfl

theorem V_le_Y {j : ℕ} (hj : j < 8) {c : Fin 4} (hA : labIn j (tl (vA c)) = true)
    (hB : labIn j (tl (vB c)) = true) : V c ≤ Y j := by
  rw [← V_eq_closure, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact mem_Y_of_labIn hj hA
  · exact mem_Y_of_labIn hj hB

theorem complete (Z : Subgroup G22) (hZ : P0 ⊔ V 0 ≤ Z) : Z = ⊤ ∨ ∃ j < 8, Z = Y j := by
  obtain ⟨j, hj, rfl⟩ := m22c_complete Z (by rw [closure_sg]; exact hZ)
  rw [mw_len] at hj ⊢
  unfold memberOrTop
  split_ifs with hj8
  · exact Or.inr ⟨j, hj8, rfl⟩
  · exact Or.inl rfl

theorem A_zero : A 0 = Y 1 := by
  have h := labK
  simp only [Bool.and_eq_true] at h
  refine Subgroup.eq_of_le_of_card_ge (sup_le (le_sup_right.trans (sg_le_Y 1))
    (V_le_Y (c := 2) (by norm_num) h.1.1.1 h.1.1.2)) ?_
  rw [card_Y (by norm_num), card_A]
  rfl

theorem A_one : A 1 = Y 2 := by
  have h := labK
  simp only [Bool.and_eq_true] at h
  refine Subgroup.eq_of_le_of_card_ge (sup_le (le_sup_right.trans (sg_le_Y 2))
    (V_le_Y (c := 3) (by norm_num) h.1.2 h.2)) ?_
  rw [card_Y (by norm_num), card_A]
  rfl

theorem normalizer_R : Subgroup.normalizer (R 0 : Set G22) = Y 3 := by
  have hSR : P0 ⊔ V 0 ≤ Subgroup.normalizer (R 0 : Set G22) :=
    sup_le (P0_le_normalizer_R 0) ((le_sup_left : V 0 ≤ R 0).trans Subgroup.le_normalizer)
  have hc := card_normalizer_R 0
  rcases complete _ hSR with h | ⟨j, hj, h⟩
  · rw [h, Subgroup.card_top, card_M22] at hc
    norm_num at hc
  · rw [h, card_Y hj] at hc
    obtain rfl : j = 3 := by
      interval_cases j <;> first | rfl | (exfalso; revert hc; decide)
    exact h

theorem m22c_facts : ∀ Z : Subgroup G22, P0 ⊔ V 0 ≤ Z →
    Z = ⊤ ∨ Z = A 0 ∨ Z = A 1 ∨ Z = Subgroup.normalizer (R 0 : Set G22) ∨ Nat.card Z ∣ 576 := by
  intro Z hZ
  rcases complete Z hZ with h | ⟨j, hj, rfl⟩
  · exact Or.inl h
  · right
    have hc := card_Y hj
    interval_cases j
    · exact Or.inr (Or.inr (Or.inr (by rw [hc]; decide)))
    · exact Or.inl A_zero.symm
    · exact Or.inr (Or.inl A_one.symm)
    · exact Or.inr (Or.inr (Or.inl normalizer_R.symm))
    all_goals exact Or.inr (Or.inr (Or.inr (by rw [hc]; decide)))

end CFSG.KD.R148Dc.M22C

end
