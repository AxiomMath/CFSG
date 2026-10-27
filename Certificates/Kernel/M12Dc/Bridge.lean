module

public import Certificates.Kernel.M12Dc.Checks
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.Background.HSporLatInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M12Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (m12a m12b card_M12 m12_hyp)

abbrev G : Type := ↥CFSG.Blueprint.NativeSporadic.M12

theorem tabsB : (J.tabs == [m12ta, m12tb, (m12SLP[172]!).toList, (m12SLP[187]!).toList,
    (m12SLP[202]!).toList, (m12SLP[211]!).toList, (m12SLP[212]!).toList,
    (m12SLP[213]!).toList]) = true := by
  quickRfl

theorem tabs_eq : J.tabs = [m12ta, m12tb, (m12SLP[172]!).toList, (m12SLP[187]!).toList,
    (m12SLP[202]!).toList, (m12SLP[211]!).toList, (m12SLP[212]!).toList,
    (m12SLP[213]!).toList] := eq_of_beq tabsB

theorem tab_ok {l : ℕ} (hl : l < 8) :
    (J.tabs.getD l []).length = 12 ∧ ∀ p ∈ J.tabs.getD l [], p < 12 := by
  have h := tabsOK
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hl' : l < J.tabs.length := by rw [Nat.eq_of_beq_eq_true h.1]; exact hl
  have hm : J.tabs.getD l [] ∈ J.tabs := by
    rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl'
  have e := h.2 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at e
  exact e

theorem good_tabF {x : G} {t : List ℕ} (hx : (tab 12 x).toArray = t.toArray)
    (ht : t.length = 12 ∧ ∀ p ∈ t, p < 12) : Good 12 (tab 12 x).toArray (tabF t) := by
  rw [hx]
  refine ⟨by simp [ht.1], fun p hp => ⟨?_, ?_⟩⟩
  · simp [tabF, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have hp' : p < t.length := by rw [ht.1]; exact hp
    rw [tabF, List.getD_eq_getElem _ _ hp']
    exact ht.2 _ (List.getElem_mem hp')

@[irreducible] noncomputable def E (j : ℕ) : G := (slpElts m12a m12b m12Prog).getD j 1

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem m12_ta : (tab 12 m12a).toArray = m12ta.toArray := by rw [m12_tab_a]

theorem m12_tb : (tab 12 m12b).toArray = m12tb.toArray := by rw [m12_tab_b]


theorem tab_node {j : ℕ} (hj : j < m12Prog.length + 2) :
    (tab 12 (E j)).toArray = m12SLP[j]! := by
  have hinv := slp_foldl_inv (n := 12) m12Prog #[m12a, m12b]
    #[(tab 12 m12a).toArray, (tab 12 m12b).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using m12_valid)
  have hs : j < (m12Prog.foldl slpStepA #[(tab 12 m12a).toArray, (tab 12 m12b).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : m12Prog.foldl slpStepA #[(tab 12 m12a).toArray, (tab 12 m12b).toArray] = m12SLP := by
    rw [m12_ta, m12_tb]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

@[expose] noncomputable def sl : List G := [E 172, E 187, E 202, E 211, E 212, E 213]

theorem tab_letter {l : ℕ} (hl : l < 8) :
    (tab 12 ((m12a :: m12b :: sl).getD l 1)).toArray = (J.tabs.getD l []).toArray := by
  rw [tabs_eq]
  interval_cases l
  · exact m12_ta
  · exact m12_tb
  all_goals
    change (tab 12 (E _)).toArray = _
    rw [tab_node (by decide)]
    simp

theorem good0 {l : ℕ} (hl : l < 8) :
    Good 12 (tab 12 ((m12a :: m12b :: sl).getD l 1)).toArray (L0 l) :=
  good_tabF (tab_letter hl) (tab_ok hl)

theorem hL : ∀ l < 2 + C.ns,
    Good (12 * 12) (@tab G _ (12 * 12) (pairAction G 12) ((m12a :: m12b :: sl).getD l 1)).toArray
      (C.L l) :=
  fun l hl => good_pair (good0 (l := l) hl)

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 12 (tab 12 x).toArray f) {p : ℕ}
    (hp : p < 12) : act 12 x p = f p ∧ f p < 12 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 12 (tab 12 x).toArray f)
    (hy : Good 12 (tab 12 y).toArray g) (h : ∀ p < 12, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := 12)
  intro b hb
  have hb' := List.mem_range.1 hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact h b hb'

@[expose] noncomputable def m12Sg : List G :=
  m12Qp.map fun p => (slpElts m12a m12b m12Prog).getD p.1 1

theorem m12Sg_eq : m12Sg = [E 172, E 187, E 202] := by
  simp only [m12Sg, m12Qp, List.map_cons, List.map_nil, E]

theorem htake : sl.take 3 = m12Sg := by
  rw [m12Sg_eq]
  rfl

theorem m12_sGens : genTabs 12 m12Sg = m12STabs ∧
    Nat.card (Subgroup.closure {x | x ∈ m12Sg}) = 2 ^ 6 := by
  have hc : BaseCertS 12 (List.range 12)
      (slpTabsA (tab 12 m12a).toArray (tab 12 m12b).toArray m12Prog) m12Qp
      153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 := by
    rw [m12_ta, m12_tb]
    exact m12_cert
  have := sGens_of_baseCertS (n := 12) (List.range 12) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m12a m12b m12Prog m12_valid m12Qp 153 204 208 206 210 m12Enum.1
    m12Enum.2.1 m12Enum.2.2 6 hc
  refine ⟨?_, this.2⟩
  rw [m12Sg, this.1, m12_ta, m12_tb]
  rfl

theorem hinvL : ∀ i < 3, ∀ p < 12, L0 (Nat.add 5 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  have hg : ∀ y ∈ [E 172, E 187, E 202], y ∈ Subgroup.closure {x | x ∈ m12Sg} :=
    fun y hy => Subgroup.subset_closure (by rw [m12Sg_eq]; exact hy)
  have hm : ∀ i < 3, (sl.getD (5 + i - 2) 1) =
      ((m12a :: m12b :: sl).getD (2 + i) 1)⁻¹ := by
    intro i hi
    have e : sl.getD (5 + i - 2) 1 = (m12a :: m12b :: sl).getD (Nat.add 5 i) 1 := by
      have : Nat.add 5 i = (5 + i - 2) + 2 := by change 5 + i = 5 + i - 2 + 2; omega
      rw [this]
      rfl
    rw [e]
    exact eq_inv_of_maps (good0 (by change 5 + i < 8; omega)) (good0 (by omega))
      (hinvL i hi)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · rw [show E 211 = ((m12a :: m12b :: sl).getD 2 1)⁻¹ from hm 0 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 212 = ((m12a :: m12b :: sl).getD 3 1)⁻¹ from hm 1 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 213 = ((m12a :: m12b :: sl).getD 4 1)⁻¹ from hm 2 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))

theorem sepB : (D.sep == (List.range 12).map (fun i => i + 12 * i)) = true := by quickRfl

theorem hsep : ∀ g : G, (∀ p ∈ D.sep, @act G _ (12 * 12) (pairAction G 12) g p = p) → g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact sep_pair base_of_faithful g hg

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_complete : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m12Sg} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ m12Sg ++ (J.mw.getD j []).map (wordElt m12a m12b)}) j := by
  have h := @dcCheck_sound G _ _ (12 * 12) (pairAction G 12) C rfl D m12a m12b m12_hyp.gen sl rfl
    hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 6
        rw [htake]; exact m12_sGens.2)
    (by change Nat.card G = 1485 * 2 ^ 6; rw [card_M12]; norm_num) hsep (by decide) dc_ok
  have h := h.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 3} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 3 ++ (D.mw.getD j []).map (wordElt m12a m12b)}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.M12Dc

end
