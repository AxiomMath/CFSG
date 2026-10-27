module

public import Certificates.Kernel.R148Dc.M22CChecks
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.Certificates.Kernel.SporLatDcGood
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BM22Sg
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Sporadic.Mathieu.M22
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.Asc83Table.PermTables

set_option maxRecDepth 100000

public section

namespace CFSG.KD.R148Dc.M22C

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m22a m22b card_M22 m22_hyp)
open CFSG.RankThree.PartTwo.KFacts.KP4 (G22 vAE vBE)
open CFSG.RankThree.PartTwo.Sec14.Ronan148B.M22 (sg closure_sg card_P0_sup_V)
open CFSG.RankThree.Asc83Table.M22 (X Y)

theorem tab_ok {l : ℕ} (hl : l < 10) :
    (J.tabs.getD l []).length = 22 ∧ ∀ p ∈ J.tabs.getD l [], p < 22 := by
  have h := tabsOK
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hl' : l < J.tabs.length := by rw [Nat.eq_of_beq_eq_true h.1]; exact hl
  have hm : J.tabs.getD l [] ∈ J.tabs := by
    rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl'
  have e := h.2 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at e
  exact e

theorem good_tabF {x : G22} {t : List ℕ} (hx : (tab 22 x).toArray = t.toArray)
    (ht : t.length = 22 ∧ ∀ p ∈ t, p < 22) : Good 22 (tab 22 x).toArray (tabF t) := by
  rw [hx]
  refine ⟨by simp [ht.1], fun p hp => ⟨?_, ?_⟩⟩
  · simp [tabF, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have hp' : p < t.length := by rw [ht.1]; exact hp
    rw [tabF, List.getD_eq_getElem _ _ hp']
    exact ht.2 _ (List.getElem_mem hp')


theorem tabsB : (J.tabs.take 6 == [m22ta, m22tb, tab 22 X, tab 22 Y, tab 22 (vAE 0),
    tab 22 (vBE 0)]) = true := by
  quickRfl

@[expose] noncomputable def sl : List G22 := sg ++ sg.map (·⁻¹)

theorem sl_getD_hi {i : ℕ} (hi : i < 4) :
    (m22a :: m22b :: sl).getD (6 + i) 1 = ((m22a :: m22b :: sl).getD (2 + i) 1)⁻¹ := by
  interval_cases i <;> rfl

theorem tab_letter {l : ℕ} (hl : l < 6) :
    (tab 22 ((m22a :: m22b :: sl).getD l 1)).toArray = (J.tabs.getD l []).toArray := by
  have e : J.tabs.getD l [] = (J.tabs.take 6).getD l [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hl]
  rw [e, eq_of_beq tabsB]
  interval_cases l
  · change (tab 22 m22a).toArray = m22ta.toArray
    rw [m22_tab_a]
  · change (tab 22 m22b).toArray = m22tb.toArray
    rw [m22_tab_b]
  all_goals rfl

theorem hinvL : ∀ i < 4, ∀ p < 22, L0 (Nat.add 6 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem good0 {l : ℕ} (hl : l < 10) :
    Good 22 (tab 22 ((m22a :: m22b :: sl).getD l 1)).toArray (L0 l) := by
  rcases Nat.lt_or_ge l 6 with h6 | h6
  · exact good_tabF (tab_letter h6) (tab_ok (by omega))
  · obtain ⟨i, rfl⟩ : ∃ i, l = 6 + i := ⟨l - 6, by omega⟩
    rw [sl_getD_hi (by omega)]
    exact good_inv (good_tabF (tab_letter (l := 2 + i) (by omega)) (tab_ok (by omega)))
      (hinvL i (by omega))

theorem hL : ∀ l < 2 + C.ns,
    Good (22 * 22) (@tab G22 _ (22 * 22) (pairAction G22 22) ((m22a :: m22b :: sl).getD l 1)).toArray
      (C.L l) :=
  fun l hl => good_pair (good0 (l := l) hl)

theorem htake : sl.take 4 = sg := rfl

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 4}
  rw [htake]
  rcases List.mem_append.1 hx with h | h
  · exact Subgroup.subset_closure h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact Subgroup.inv_mem _ (Subgroup.subset_closure hy)

theorem sepB : (D.sep == (List.range 22).map (fun i => i + 22 * i)) = true := by quickRfl

theorem hsep : ∀ g : G22, (∀ p ∈ D.sep, @act G22 _ (22 * 22) (pairAction G22 22) g p = p) →
    g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact sep_pair base_of_faithful g hg

theorem dc_ok : dcCheckS C D 36 = true := by
  unfold dcCheckS
  rw [glob, pts, orbs, chunks]
  rfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl


theorem dc_sound :
    (∀ g : G22, @lab G22 _ (List ℕ) (22 * 22) (pairAction G22 22) ptLab C.Δ g = C.Δ ↔
      g ∈ Subgroup.closure {x | x ∈ sl.take C.ng}) ∧
    ∀ Z : Subgroup G22, Subgroup.closure {x | x ∈ sl.take C.ng} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length
        (fun j => Subgroup.closure {x | x ∈ sl.take C.ng ++ (D.mw.getD j []).map
          (wordElt m22a m22b)}) j :=
  @dcCheckS_sound G22 _ _ (22 * 22) (pairAction G22 22) C rfl D 36 m22a m22b m22_hyp.gen sl rfl
    hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 4}) = 36
        rw [htake, closure_sg]; exact card_P0_sup_V)
    (by change Nat.card G22 = 12320 * 36; rw [card_M22]) hsep (by decide) dc_ok

theorem m22c_stab : ∀ g : G22,
    @lab G22 _ (List ℕ) (22 * 22) (pairAction G22 22) ptLab J.delta g = J.delta ↔
      g ∈ Subgroup.closure {x | x ∈ sg} := by
  have h := dc_sound.1
  change ∀ g : G22, @lab G22 _ (List ℕ) (22 * 22) (pairAction G22 22) ptLab J.delta g =
      J.delta ↔ g ∈ Subgroup.closure {x | x ∈ sl.take 4} at h
  rw [htake] at h
  exact h

theorem m22c_complete : ∀ Z : Subgroup G22, Subgroup.closure {x | x ∈ sg} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ sg ++ (J.mw.getD j []).map (wordElt m22a m22b)}) j := by
  have h := dc_sound.2
  change ∀ Z : Subgroup G22, Subgroup.closure {x | x ∈ sl.take 4} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 4 ++ (D.mw.getD j []).map (wordElt m22a m22b)}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.R148Dc.M22C

end
