module

public import Certificates.Kernel.M11Dc.Checks
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M11Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGSporLat
open CFSG.Sporadic.Mathieu (m11a m11b card_M11 m11_hyp)

abbrev G : Type := ↥CFSG.Blueprint.NativeSporadic.M11

theorem tabsB : (J.tabs == [m11ta, m11tb, (m11SLP[178]!).toList, (m11SLP[187]!).toList,
    (m11SLP[196]!).toList, (m11SLP[201]!).toList]) = true := by
  quickRfl

theorem tabs_eq : J.tabs = [m11ta, m11tb, (m11SLP[178]!).toList, (m11SLP[187]!).toList,
    (m11SLP[196]!).toList, (m11SLP[201]!).toList] := eq_of_beq tabsB

theorem tab_ok {l : ℕ} (hl : l < 6) :
    (J.tabs.getD l []).length = 11 ∧ ∀ p ∈ J.tabs.getD l [], p < 11 := by
  have h := tabsOK
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hl' : l < J.tabs.length := by rw [Nat.eq_of_beq_eq_true h.1]; exact hl
  have hm : J.tabs.getD l [] ∈ J.tabs := by
    rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl'
  have e := h.2 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at e
  exact e

theorem good_tabF {x : G} {t : List ℕ} (hx : (tab 11 x).toArray = t.toArray)
    (ht : t.length = 11 ∧ ∀ p ∈ t, p < 11) : Good 11 (tab 11 x).toArray (tabF t) := by
  rw [hx]
  refine ⟨by simp [ht.1], fun p hp => ⟨?_, ?_⟩⟩
  · simp [tabF, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have hp' : p < t.length := by rw [ht.1]; exact hp
    rw [tabF, List.getD_eq_getElem _ _ hp']
    exact ht.2 _ (List.getElem_mem hp')

@[irreducible] noncomputable def E (j : ℕ) : G := (slpElts m11a m11b m11Prog).getD j 1

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem m11_ta : (tab 11 m11a).toArray = m11ta.toArray := by rw [m11_tab_a]

theorem m11_tb : (tab 11 m11b).toArray = m11tb.toArray := by rw [m11_tab_b]


theorem tab_node {j : ℕ} (hj : j < m11Prog.length + 2) :
    (tab 11 (E j)).toArray = m11SLP[j]! := by
  have hinv := slp_foldl_inv (n := 11) m11Prog #[m11a, m11b]
    #[(tab 11 m11a).toArray, (tab 11 m11b).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using m11_valid)
  have hs : j < (m11Prog.foldl slpStepA #[(tab 11 m11a).toArray, (tab 11 m11b).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : m11Prog.foldl slpStepA #[(tab 11 m11a).toArray, (tab 11 m11b).toArray] = m11SLP := by
    rw [m11_ta, m11_tb]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

@[expose] noncomputable def sl : List G := [E 178, E 187, E 196, E 201]

theorem tab_letter {l : ℕ} (hl : l < 6) :
    (tab 11 ((m11a :: m11b :: sl).getD l 1)).toArray = (J.tabs.getD l []).toArray := by
  rw [tabs_eq]
  interval_cases l
  · exact m11_ta
  · exact m11_tb
  all_goals
    change (tab 11 (E _)).toArray = _
    rw [tab_node (by decide)]
    simp

theorem good0 {l : ℕ} (hl : l < 6) :
    Good 11 (tab 11 ((m11a :: m11b :: sl).getD l 1)).toArray (L0 l) :=
  good_tabF (tab_letter hl) (tab_ok hl)

theorem hL : ∀ l < 2 + C.ns,
    Good (11 * 11) (@tab G _ (11 * 11) (pairAction G 11) ((m11a :: m11b :: sl).getD l 1)).toArray
      (C.L l) :=
  fun l hl => good_pair (good0 (l := l) hl)

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 11 (tab 11 x).toArray f) {p : ℕ}
    (hp : p < 11) : act 11 x p = f p ∧ f p < 11 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 11 (tab 11 x).toArray f)
    (hy : Good 11 (tab 11 y).toArray g) (h : ∀ p < 11, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := 11)
  intro b hb
  have hb' := List.mem_range.1 hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact h b hb'

@[expose] noncomputable def m11SgK : List G :=
  m11Qp.map fun p => (slpElts m11a m11b m11Prog).getD p.1 1

theorem m11SgK_eq : m11SgK = [E 178, E 187] := by
  simp only [m11SgK, m11Qp, List.map_cons, List.map_nil, E]

theorem htake : sl.take 2 = m11SgK := by
  rw [m11SgK_eq]
  rfl

theorem m11_sGensK : genTabs 11 m11SgK = m11STabs ∧
    Nat.card (Subgroup.closure {x | x ∈ m11SgK}) = 2 ^ 4 := by
  have hc : BaseCertS 11 (List.range 11)
      (slpTabsA (tab 11 m11a).toArray (tab 11 m11b).toArray m11Prog) m11Qp
      159 189 193 191 195 m11Enum.1 m11Enum.2.1 m11Enum.2.2 4 := by
    rw [m11_ta, m11_tb]
    exact m11_cert
  have := sGens_of_baseCertS (n := 11) (List.range 11) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m11a m11b m11Prog m11_valid m11Qp 159 189 193 191 195 m11Enum.1
    m11Enum.2.1 m11Enum.2.2 4 hc
  refine ⟨?_, this.2⟩
  rw [m11SgK, this.1, m11_ta, m11_tb]
  rfl

theorem hinvL : ∀ i < 2, ∀ p < 11, L0 (Nat.add 4 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 2}
  rw [htake]
  have hg : ∀ y ∈ [E 178, E 187], y ∈ Subgroup.closure {x | x ∈ m11SgK} :=
    fun y hy => Subgroup.subset_closure (by rw [m11SgK_eq]; exact hy)
  have hm : ∀ i < 2, (sl.getD (4 + i - 2) 1) =
      ((m11a :: m11b :: sl).getD (2 + i) 1)⁻¹ := by
    intro i hi
    have e : sl.getD (4 + i - 2) 1 = (m11a :: m11b :: sl).getD (Nat.add 4 i) 1 := by
      have : Nat.add 4 i = (4 + i - 2) + 2 := by change 4 + i = 4 + i - 2 + 2; omega
      rw [this]
      rfl
    rw [e]
    exact eq_inv_of_maps (good0 (by change 4 + i < 6; omega)) (good0 (by omega))
      (hinvL i hi)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · rw [show E 196 = ((m11a :: m11b :: sl).getD 2 1)⁻¹ from hm 0 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 201 = ((m11a :: m11b :: sl).getD 3 1)⁻¹ from hm 1 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))

theorem sepB : (D.sep == (List.range 11).map (fun i => i + 11 * i)) = true := by quickRfl

theorem hsep : ∀ g : G, (∀ p ∈ D.sep, @act G _ (11 * 11) (pairAction G 11) g p = p) → g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact sep_pair base_of_faithful g hg

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_complete : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m11SgK} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ m11SgK ++ (J.mw.getD j []).map (wordElt m11a m11b)}) j := by
  have h := @dcCheck_sound G _ _ (11 * 11) (pairAction G 11) C rfl D m11a m11b m11_hyp.gen sl rfl
    hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 2}) = 2 ^ 4
        rw [htake]; exact m11_sGensK.2)
    (by change Nat.card G = 495 * 2 ^ 4; rw [card_M11]; norm_num) hsep (by decide) dc_ok
  have h := h.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 2} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 2 ++ (D.mw.getD j []).map (wordElt m11a m11b)}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.M11Dc

end
