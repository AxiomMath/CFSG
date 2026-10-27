module

public import Certificates.Kernel.M23Dc.Checks
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.Background.HSporLatInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card m23_eq_closure)

abbrev G : Type := ↥CFSG.Blueprint.NativeSporadic.M23

theorem tabsB : (J.tabs == [m23ta, m23tb, (m23SLP[167]!).toList, (m23SLP[188]!).toList,
    (m23SLP[197]!).toList, (m23SLP[209]!).toList, (m23SLP[210]!).toList,
    (m23SLP[215]!).toList]) = true := by
  quickRfl

theorem tabs_eq : J.tabs = [m23ta, m23tb, (m23SLP[167]!).toList, (m23SLP[188]!).toList,
    (m23SLP[197]!).toList, (m23SLP[209]!).toList, (m23SLP[210]!).toList,
    (m23SLP[215]!).toList] := eq_of_beq tabsB

theorem tab_ok {l : ℕ} (hl : l < 8) :
    (J.tabs.getD l []).length = 23 ∧ ∀ p ∈ J.tabs.getD l [], p < 23 := by
  have h := tabsOK
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hl' : l < J.tabs.length := by rw [Nat.eq_of_beq_eq_true h.1]; exact hl
  have hm : J.tabs.getD l [] ∈ J.tabs := by
    rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl'
  have e := h.2 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at e
  exact e

theorem good_tabF {x : G} {t : List ℕ} (hx : (tab 23 x).toArray = t.toArray)
    (ht : t.length = 23 ∧ ∀ p ∈ t, p < 23) : Good 23 (tab 23 x).toArray (tabF t) := by
  rw [hx]
  refine ⟨by simp [ht.1], fun p hp => ⟨?_, ?_⟩⟩
  · simp [tabF, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have hp' : p < t.length := by rw [ht.1]; exact hp
    rw [tabF, List.getD_eq_getElem _ _ hp']
    exact ht.2 _ (List.getElem_mem hp')

@[irreducible] noncomputable def E (j : ℕ) : G := (slpElts m23GenA m23GenB m23Prog).getD j 1

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem m23_ta : (tab 23 m23GenA).toArray = m23ta.toArray := by rw [m23_tab_a]

theorem m23_tb : (tab 23 m23GenB).toArray = m23tb.toArray := by rw [m23_tab_b]

theorem m23_gen : Subgroup.closure ({m23GenA, m23GenB} : Set G) = ⊤ :=
  CFSG.Sporadic.Mathieu.closure_pair_eq_top m23_eq_closure _ _


theorem tab_node {j : ℕ} (hj : j < m23Prog.length + 2) :
    (tab 23 (E j)).toArray = m23SLP[j]! := by
  have hinv := slp_foldl_inv (n := 23) m23Prog #[m23GenA, m23GenB]
    #[(tab 23 m23GenA).toArray, (tab 23 m23GenB).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using m23_valid)
  have hs : j < (m23Prog.foldl slpStepA
      #[(tab 23 m23GenA).toArray, (tab 23 m23GenB).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : m23Prog.foldl slpStepA #[(tab 23 m23GenA).toArray, (tab 23 m23GenB).toArray] =
      m23SLP := by
    rw [m23_ta, m23_tb]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

@[expose] noncomputable def sl : List G := [E 167, E 188, E 197, E 209, E 210, E 215]

theorem tab_letter {l : ℕ} (hl : l < 8) :
    (tab 23 ((m23GenA :: m23GenB :: sl).getD l 1)).toArray = (J.tabs.getD l []).toArray := by
  rw [tabs_eq]
  interval_cases l
  · exact m23_ta
  · exact m23_tb
  all_goals
    change (tab 23 (E _)).toArray = _
    rw [tab_node (by decide)]
    simp

theorem good0 {l : ℕ} (hl : l < 8) :
    Good 23 (tab 23 ((m23GenA :: m23GenB :: sl).getD l 1)).toArray (L0 l) :=
  good_tabF (tab_letter hl) (tab_ok hl)

theorem hL : ∀ l < 2 + C.ns,
    Good (23 * 23) (@tab G _ (23 * 23) (pairAction G 23)
      ((m23GenA :: m23GenB :: sl).getD l 1)).toArray (C.L l) :=
  fun l hl => good_pair (good0 (l := l) hl)

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 23 (tab 23 x).toArray f) {p : ℕ}
    (hp : p < 23) : act 23 x p = f p ∧ f p < 23 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 23 (tab 23 x).toArray f)
    (hy : Good 23 (tab 23 y).toArray g) (h : ∀ p < 23, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := 23)
  intro b hb
  have hb' := List.mem_range.1 hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact h b hb'

@[expose] noncomputable def m23Sg : List G :=
  m23Qp.map fun p => (slpElts m23GenA m23GenB m23Prog).getD p.1 1

theorem m23Sg_eq : m23Sg = [E 167, E 188, E 197] := by
  simp only [m23Sg, m23Qp, List.map_cons, List.map_nil, E]

theorem htake : sl.take 3 = m23Sg := by
  rw [m23Sg_eq]
  rfl

theorem m23_sGens : genTabs 23 m23Sg = m23STabs ∧
    Nat.card (Subgroup.closure {x | x ∈ m23Sg}) = 2 ^ 7 := by
  have hc : BaseCertS 23 (List.range 23)
      (slpTabsA (tab 23 m23GenA).toArray (tab 23 m23GenB).toArray m23Prog) m23Qp
      159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 := by
    rw [m23_ta, m23_tb]
    exact m23_cert
  have := sGens_of_baseCertS (n := 23) (List.range 23) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m23GenA m23GenB m23Prog m23_valid m23Qp 159 199 203 201 205 m23Enum.1
    m23Enum.2.1 m23Enum.2.2 7 hc
  refine ⟨?_, this.2⟩
  rw [m23Sg, this.1, m23_ta, m23_tb]
  rfl

theorem hinvL : ∀ i < 3, ∀ p < 23, L0 (Nat.add 5 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  have hg : ∀ y ∈ [E 167, E 188, E 197], y ∈ Subgroup.closure {x | x ∈ m23Sg} :=
    fun y hy => Subgroup.subset_closure (by rw [m23Sg_eq]; exact hy)
  have hm : ∀ i < 3, sl.getD (Nat.add 3 i) 1 =
      ((m23GenA :: m23GenB :: sl).getD (Nat.add 2 i) 1)⁻¹ := by
    intro i hi
    have e : sl.getD (Nat.add 3 i) 1 = (m23GenA :: m23GenB :: sl).getD (Nat.add 5 i) 1 := by
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
  · rw [show E 209 = ((m23GenA :: m23GenB :: sl).getD 2 1)⁻¹ from hm 0 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 210 = ((m23GenA :: m23GenB :: sl).getD 3 1)⁻¹ from hm 1 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 215 = ((m23GenA :: m23GenB :: sl).getD 4 1)⁻¹ from hm 2 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))

theorem sepB : (D.sep == (List.range 23).map (fun i => i + 23 * i)) = true := by quickRfl

theorem hsep : ∀ g : G, (∀ p ∈ D.sep, @act G _ (23 * 23) (pairAction G 23) g p = p) → g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact sep_pair base_of_faithful g hg

theorem ch_of {i : Nat} (hi : i < 8) : chunkOK C D i = true := K.all i hi

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  have hl : D.Rc.length = 8 := rfl
  rw [hl, List.all_eq_true]
  intro i hi
  exact ch_of (List.mem_range.1 hi)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_complete : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m23Sg} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ m23Sg ++ (J.mw.getD j []).map
        (wordElt m23GenA m23GenB)}) j := by
  have h := @dcCheck_sound G _ _ (23 * 23) (pairAction G 23) C rfl D m23GenA m23GenB m23_gen sl
    rfl hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 7
        rw [htake]; exact m23_sGens.2)
    (by change Nat.card G = 79695 * 2 ^ 7; rw [m23_card]; norm_num) hsep (by decide) dc_ok
  have h := h.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 3} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 3 ++ (D.mw.getD j []).map (wordElt m23GenA m23GenB)}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.M23Dc

end
