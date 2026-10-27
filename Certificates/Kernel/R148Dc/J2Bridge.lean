module

public import Certificates.Kernel.R148Dc.J2AChecks
public import Certificates.Kernel.R148Dc.J2BChecks
public import CFSG.Certificates.Kernel.SporLatDcSoundInv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Elts
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.R148Dc.J2

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ rep_x rep_z card_GJ)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (vA tJ rep_tJ)
open CFSG.ComponentClassification.J2Cover (pa pb closure_pa_pb rep_permA rep_permB autStrong)
open CFSG.Monster.B.Co2 (Rep)

theorem tab_eq_of_rep {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (hsz : t.size = 315) :
    (tab 315 g).toArray = t := by
  apply Array.ext
  · simp [tab, hsz]
  · intro i h1 h2
    have hi : i < 315 := by simpa [tab] using h1
    simp only [tab, List.getElem_toArray, List.getElem_map, List.getElem_finRange]
    rw [← getElem!_pos t i h2, ht ⟨i, hi⟩]
    rfl

theorem sizes : (autStrong[0]!.size == 315 && autStrong[1]!.size == 315 &&
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr.size == 315 &&
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr.size == 315 &&
    (List.range 18).all fun i => vA[i]!.size == 315) = true := by
  quickRfl

theorem ta_size : autStrong[0]!.size = 315 := by
  have h := sizes
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

theorem tb_size : autStrong[1]!.size = 315 := by
  have h := sizes
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem zArr_size : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr.size = 315 := by
  have h := sizes
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem xArr_size : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr.size = 315 := by
  have h := sizes
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem vA_size {i : ℕ} (hi : i < 18) : vA[i]!.size = 315 := by
  have h := sizes
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h.2 i (List.mem_range.2 hi)


theorem tab_pa : (tab 315 pa).toArray = autStrong[0]! := tab_eq_of_rep rep_permA ta_size

theorem tab_pb : (tab 315 pb).toArray = autStrong[1]! := tab_eq_of_rep rep_permB tb_size

theorem tab_z : (tab 315 zJ).toArray = CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr :=
  tab_eq_of_rep rep_z zArr_size

theorem tab_x : (tab 315 xJ).toArray = CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr :=
  tab_eq_of_rep rep_x xArr_size

theorem tab_t {i : ℕ} (hi : i < 18) : (tab 315 (tJ i)).toArray = vA[i]! :=
  tab_eq_of_rep (rep_tJ hi) (vA_size hi)

theorem hN : Nat.card GJ = 16800 * 36 := by rw [card_GJ]

theorem hsepR : ∀ g : GJ, (∀ p ∈ List.range 315, act 315 g p = p) → g = 1 :=
  base_of_faithful

end CFSG.KD.R148Dc.J2

namespace CFSG.KD.R148Dc.J2A

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KD.R148Dc.J2
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (vA tJ)
open CFSG.ComponentClassification.J2Cover (pa pb closure_pa_pb autStrong)

theorem tabsB : (J.tabs.take 6 == [autStrong[0]!.toList, autStrong[1]!.toList,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr.toList,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr.toList, vA[0]!.toList, vA[1]!.toList]) =
    true := by
  quickRfl

theorem tabL {l : ℕ} (hl : l < 10) : J.tabs.getD l [] = (List.range 315).map (L l) :=
  beq_iff_eq.1 (List.all_eq_true.1 tabsC l (List.mem_range.2 hl))

theorem hinv : ∀ i < 4, ∀ p < 315, C.L (2 + 4 + i) (C.L (2 + i) p) = p := fun i hi p hp =>
  beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem sepB : (D.sep == List.range 315) = true := by quickRfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_ok : dcCheckS C D 36 = true := by
  unfold dcCheckS
  rw [glob, pts, orbs, chunks]
  rfl

theorem deltaV : PtValid 315 C.Δ := by decide


@[expose] noncomputable def sgA : List GJ := [zJ, xJ, tJ 0, tJ 1]

theorem hL : ∀ l < 2 + sgA.length,
    Good 315 (tab 315 ((pa :: pb :: sgA).getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 6 := hl
  refine good_of_tab ?_
  have e : (List.range 315).map (C.L l) = (J.tabs.take 6).getD l [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hl', ← List.getD_eq_getElem?_getD,
      tabL (by omega)]
    rfl
  rw [e, eq_of_beq tabsB]
  interval_cases l
  · exact tab_pa
  · exact tab_pb
  · exact tab_z
  · exact tab_x
  · exact tab_t (i := 0) (by norm_num)
  · exact tab_t (i := 1) (by norm_num)

theorem dc_sound (hk : Nat.card (Subgroup.closure {x | x ∈ sgA}) = 36) :
    (∀ g : GJ, lab 315 ptLab J.delta g = J.delta ↔ g ∈ Subgroup.closure {x | x ∈ sgA}) ∧
    ∀ Z : Subgroup GJ, Subgroup.closure {x | x ∈ sgA} ≤ Z → ∃ j ≤ J.mw.length,
      Z = memberOrTop J.mw.length
        (fun j => Subgroup.closure {x | x ∈ sgA ++ (J.mw.getD j []).map (wordElt pa pb)}) j := by
  have h := dcCheckS_sound_inv (n := 315) C rfl D 36 pa pb closure_pa_pb sgA rfl rfl hL hinv hk hN
    (fun g hg => hsepR g (by rw [← eq_of_beq sepB]; exact hg)) deltaV dc_ok
  rw [eq_of_beq hmwB] at h
  exact h

end CFSG.KD.R148Dc.J2A

namespace CFSG.KD.R148Dc.J2B

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KD.R148Dc.J2
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (vA tJ)
open CFSG.ComponentClassification.J2Cover (pa pb closure_pa_pb autStrong)

theorem tabsB : (J.tabs.take 6 == [autStrong[0]!.toList, autStrong[1]!.toList,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr.toList,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr.toList, vA[9]!.toList, vA[10]!.toList]) =
    true := by
  quickRfl

theorem tabL {l : ℕ} (hl : l < 10) : J.tabs.getD l [] = (List.range 315).map (L l) :=
  beq_iff_eq.1 (List.all_eq_true.1 tabsC l (List.mem_range.2 hl))

theorem hinv : ∀ i < 4, ∀ p < 315, C.L (2 + 4 + i) (C.L (2 + i) p) = p := fun i hi p hp =>
  beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem sepB : (D.sep == List.range 315) = true := by quickRfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_ok : dcCheckS C D 36 = true := by
  unfold dcCheckS
  rw [glob, pts, orbs, chunks]
  rfl

theorem deltaV : PtValid 315 C.Δ := by decide


@[expose] noncomputable def sgB : List GJ := [zJ, xJ, tJ 9, tJ 10]

theorem hL : ∀ l < 2 + sgB.length,
    Good 315 (tab 315 ((pa :: pb :: sgB).getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 6 := hl
  refine good_of_tab ?_
  have e : (List.range 315).map (C.L l) = (J.tabs.take 6).getD l [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hl', ← List.getD_eq_getElem?_getD,
      tabL (by omega)]
    rfl
  rw [e, eq_of_beq tabsB]
  interval_cases l
  · exact tab_pa
  · exact tab_pb
  · exact tab_z
  · exact tab_x
  · exact tab_t (i := 9) (by norm_num)
  · exact tab_t (i := 10) (by norm_num)

theorem dc_sound (hk : Nat.card (Subgroup.closure {x | x ∈ sgB}) = 36) :
    (∀ g : GJ, lab 315 ptLab J.delta g = J.delta ↔ g ∈ Subgroup.closure {x | x ∈ sgB}) ∧
    ∀ Z : Subgroup GJ, Subgroup.closure {x | x ∈ sgB} ≤ Z → ∃ j ≤ J.mw.length,
      Z = memberOrTop J.mw.length
        (fun j => Subgroup.closure {x | x ∈ sgB ++ (J.mw.getD j []).map (wordElt pa pb)}) j := by
  have h := dcCheckS_sound_inv (n := 315) C rfl D 36 pa pb closure_pa_pb sgB rfl rfl hL hinv hk hN
    (fun g hg => hsepR g (by rw [← eq_of_beq sepB]; exact hg)) deltaV dc_ok
  rw [eq_of_beq hmwB] at h
  exact h

end CFSG.KD.R148Dc.J2B

end
