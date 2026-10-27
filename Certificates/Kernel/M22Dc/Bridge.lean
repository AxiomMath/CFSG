module

public import Certificates.Kernel.M22Dc.Checks
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.Background.HSporLatInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M22Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (m22a m22b card_M22 m22_hyp)

abbrev G : Type := ↥CFSG.Blueprint.NativeSporadic.M22

theorem tabsB : (J.tabs == [m22ta, m22tb, (m22SLP[180]!).toList, (m22SLP[195]!).toList,
    (m22SLP[203]!).toList, (m22SLP[212]!).toList, (m22SLP[213]!).toList,
    (m22SLP[217]!).toList]) = true := by
  quickRfl

theorem tabs_eq : J.tabs = [m22ta, m22tb, (m22SLP[180]!).toList, (m22SLP[195]!).toList,
    (m22SLP[203]!).toList, (m22SLP[212]!).toList, (m22SLP[213]!).toList,
    (m22SLP[217]!).toList] := eq_of_beq tabsB

theorem tab_ok {l : ℕ} (hl : l < 8) :
    (J.tabs.getD l []).length = 22 ∧ ∀ p ∈ J.tabs.getD l [], p < 22 := by
  have h := tabsOK
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hl' : l < J.tabs.length := by rw [Nat.eq_of_beq_eq_true h.1]; exact hl
  have hm : J.tabs.getD l [] ∈ J.tabs := by
    rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl'
  have e := h.2 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at e
  exact e

theorem good_tabF {x : G} {t : List ℕ} (hx : (tab 22 x).toArray = t.toArray)
    (ht : t.length = 22 ∧ ∀ p ∈ t, p < 22) : Good 22 (tab 22 x).toArray (tabF t) := by
  rw [hx]
  refine ⟨by simp [ht.1], fun p hp => ⟨?_, ?_⟩⟩
  · simp [tabF, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have hp' : p < t.length := by rw [ht.1]; exact hp
    rw [tabF, List.getD_eq_getElem _ _ hp']
    exact ht.2 _ (List.getElem_mem hp')

@[irreducible] noncomputable def E (j : ℕ) : G := (slpElts m22a m22b m22Prog).getD j 1

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem m22_ta : (tab 22 m22a).toArray = m22ta.toArray := by rw [m22_tab_a]

theorem m22_tb : (tab 22 m22b).toArray = m22tb.toArray := by rw [m22_tab_b]


theorem tab_node {j : ℕ} (hj : j < m22Prog.length + 2) :
    (tab 22 (E j)).toArray = m22SLP[j]! := by
  have hinv := slp_foldl_inv (n := 22) m22Prog #[m22a, m22b]
    #[(tab 22 m22a).toArray, (tab 22 m22b).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using m22_valid)
  have hs : j < (m22Prog.foldl slpStepA #[(tab 22 m22a).toArray, (tab 22 m22b).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : m22Prog.foldl slpStepA #[(tab 22 m22a).toArray, (tab 22 m22b).toArray] = m22SLP := by
    rw [m22_ta, m22_tb]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

@[expose] noncomputable def sl : List G := [E 180, E 195, E 203, E 212, E 213, E 217]

theorem tab_letter {l : ℕ} (hl : l < 8) :
    (tab 22 ((m22a :: m22b :: sl).getD l 1)).toArray = (J.tabs.getD l []).toArray := by
  rw [tabs_eq]
  interval_cases l
  · exact m22_ta
  · exact m22_tb
  all_goals
    change (tab 22 (E _)).toArray = _
    rw [tab_node (by decide)]
    simp

theorem good0 {l : ℕ} (hl : l < 8) :
    Good 22 (tab 22 ((m22a :: m22b :: sl).getD l 1)).toArray (L0 l) :=
  good_tabF (tab_letter hl) (tab_ok hl)

theorem hL : ∀ l < 2 + C.ns,
    Good (22 * 22) (@tab G _ (22 * 22) (pairAction G 22) ((m22a :: m22b :: sl).getD l 1)).toArray
      (C.L l) :=
  fun l hl => good_pair (good0 (l := l) hl)

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 22 (tab 22 x).toArray f) {p : ℕ}
    (hp : p < 22) : act 22 x p = f p ∧ f p < 22 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 22 (tab 22 x).toArray f)
    (hy : Good 22 (tab 22 y).toArray g) (h : ∀ p < 22, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := 22)
  intro b hb
  have hb' := List.mem_range.1 hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact h b hb'

@[expose] noncomputable def m22Sg : List G :=
  m22Qp.map fun p => (slpElts m22a m22b m22Prog).getD p.1 1

theorem m22Sg_eq : m22Sg = [E 180, E 195, E 203] := by
  simp only [m22Sg, m22Qp, List.map_cons, List.map_nil, E]

theorem htake : sl.take 3 = m22Sg := by
  rw [m22Sg_eq]
  rfl

theorem m22_sGens : genTabs 22 m22Sg = m22STabs ∧
    Nat.card (Subgroup.closure {x | x ∈ m22Sg}) = 2 ^ 7 := by
  have hc : BaseCertS 22 (List.range 22)
      (slpTabsA (tab 22 m22a).toArray (tab 22 m22b).toArray m22Prog) m22Qp
      163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 := by
    rw [m22_ta, m22_tb]
    exact m22_cert
  have := sGens_of_baseCertS (n := 22) (List.range 22) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m22a m22b m22Prog m22_valid m22Qp 163 205 209 207 211 m22Enum.1
    m22Enum.2.1 m22Enum.2.2 7 hc
  refine ⟨?_, this.2⟩
  rw [m22Sg, this.1, m22_ta, m22_tb]
  rfl

theorem hinvL : ∀ i < 3, ∀ p < 22, L0 (Nat.add 5 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  have hg : ∀ y ∈ [E 180, E 195, E 203], y ∈ Subgroup.closure {x | x ∈ m22Sg} :=
    fun y hy => Subgroup.subset_closure (by rw [m22Sg_eq]; exact hy)
  have hm : ∀ i < 3, sl.getD (Nat.add 3 i) 1 =
      ((m22a :: m22b :: sl).getD (Nat.add 2 i) 1)⁻¹ := by
    intro i hi
    have e : sl.getD (Nat.add 3 i) 1 = (m22a :: m22b :: sl).getD (Nat.add 5 i) 1 := by
      have : Nat.add 5 i = Nat.add 3 i + 1 + 1 := by simp only [Nat.add_eq]; omega
      rw [this, List.getD_cons_succ, List.getD_cons_succ]
    rw [e]
    exact eq_inv_of_maps (f := L0 (Nat.add 5 i)) (g := L0 (Nat.add 2 i))
      (good0 (l := Nat.add 5 i) (by simp only [Nat.add_eq]; omega))
      (good0 (l := Nat.add 2 i) (by simp only [Nat.add_eq]; omega)) (hinvL i hi)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · rw [show E 212 = ((m22a :: m22b :: sl).getD 2 1)⁻¹ from hm 0 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 213 = ((m22a :: m22b :: sl).getD 3 1)⁻¹ from hm 1 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 217 = ((m22a :: m22b :: sl).getD 4 1)⁻¹ from hm 2 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))

theorem sepB : (D.sep == (List.range 22).map (fun i => i + 22 * i)) = true := by quickRfl

theorem hsep : ∀ g : G, (∀ p ∈ D.sep, @act G _ (22 * 22) (pairAction G 22) g p = p) → g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact sep_pair base_of_faithful g hg

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_complete : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m22Sg} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ m22Sg ++ (J.mw.getD j []).map (wordElt m22a m22b)}) j := by
  have h := @dcCheck_sound G _ _ (22 * 22) (pairAction G 22) C rfl D m22a m22b m22_hyp.gen sl rfl
    hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 7
        rw [htake]; exact m22_sGens.2)
    (by change Nat.card G = 3465 * 2 ^ 7; rw [card_M22]; norm_num) hsep (by decide) dc_ok
  have h := h.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 3} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 3 ++ (D.mw.getD j []).map (wordElt m22a m22b)}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.M22Dc

end
