
module

public import Certificates.Kernel.J1Dc.Checks
public import Certificates.Kernel.J1Dc.Recs
public import Certificates.Kernel.J1Dc.Tabs
public import Certificates.Kernel.Sporadic.J1K.Final
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Quasithin.Background.E2TwoProofSporJ1Base
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J1Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Sporadic.J1 CFSG.KS.PEnum

abbrev G : Type := ↥CFSG.Sporadic.J1.J

theorem card_closure_of_list {Γ : Type} [Group Γ] (gens els : List Γ) (h1 : (1 : Γ) ∈ els)
    (hinv : ∀ g ∈ gens, g⁻¹ = g) (hmul : ∀ g ∈ gens, ∀ x ∈ els, g * x ∈ els)
    (hsub : ∀ x ∈ els, x ∈ Subgroup.closure {x | x ∈ gens}) (hnd : els.Nodup) :
    Nat.card (Subgroup.closure {x | x ∈ gens}) = els.length := by
  classical
  have hle : ∀ x ∈ Subgroup.closure {x | x ∈ gens}, x ∈ els := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact h1
    | mul_left s hs y _ ih => exact hmul s hs y ih
    | inv_mul_cancel s hs y _ ih =>
      rw [hinv s hs]
      exact hmul s hs y ih
  have hset : ((Subgroup.closure {x | x ∈ gens} : Subgroup Γ) : Set Γ) =
      ((els.toFinset : Finset Γ) : Set Γ) := by
    ext x
    simp only [SetLike.mem_coe, Finset.coe_sort_coe, List.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨hle x, hsub x⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem good_congr {n : ℕ} {t : Array ℕ} {f g : ℕ → ℕ} (h : Good n t f) (e : ∀ p < n, f p = g p) :
    Good n t g :=
  ⟨h.1, fun p hp => by rw [← e p hp]; exact h.2 p hp⟩

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 1540 (tab 1540 x).toArray f) {p : ℕ}
    (hp : p < 1540) : act 1540 x p = f p ∧ f p < 1540 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 1540 (tab 1540 x).toArray f)
    (hy : Good 1540 (tab 1540 y).toArray g) (h : ∀ p < 1540, f p = g p) : x = y := by
  have h1 : y⁻¹ * x = 1 := by
    apply base_of_faithful (n := 1540)
    intro b hb
    have hb' := List.mem_range.1 hb
    have hyi : act 1540 y⁻¹ (act 1540 y b) = b := by
      rw [← act_mul _ _ hb', inv_mul_cancel, act_one hb']
    rw [act_mul _ _ hb', (act_of_good hx hb').1, h b hb', ← (act_of_good hy hb').1]
    exact hyi
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [h1, mul_one]

theorem good_mul' {x y : G} {f g : ℕ → ℕ} (hx : Good 1540 (tab 1540 x).toArray f)
    (hy : Good 1540 (tab 1540 y).toArray g) :
    Good 1540 (tab 1540 (x * y)).toArray (fun p => f (g p)) := by
  refine ⟨by simp [tab], fun p hp => ?_⟩
  have e := img_tab (n := 1540) (x * y) p
  rw [img] at e
  rw [e, act_mul _ _ hp, (act_of_good hy hp).1, (act_of_good hx (act_of_good hy hp).2).1]
  exact ⟨rfl, (act_of_good hx (act_of_good hy hp).2).2⟩

theorem tab_ok {p : ℕ} (hp : p < 1540) : L 0 p = r32 CertificateChecks.KernelSpor.J1K.AL p ∧
    L 1 p = r32 CertificateChecks.KernelSpor.J1K.BE p ∧
    ∀ i < 3, L2 i p = wordF L (j1Words.getD i []) p := by
  have h := List.all_eq_true.1 tabsB p (List.mem_range.2 hp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem range_ok {l p : ℕ} (hl : l < 8) (hp : p < 1540) : L l p < 1540 := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 rangeB l (List.mem_range.2 hl)) p
    (List.mem_range.2 hp)
  simpa using h

theorem inv_ok {i p : ℕ} (hi : i < 3) (hp : p < 1540) :
    L2 i (L2 i p) = p ∧ L (Nat.add 5 i) p = L2 i p := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 sInvB i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem good_ta : Good 1540 j1ta.toArray (L 0) := by
  refine ⟨by simp [j1ta], fun p hp => ⟨?_, range_ok (by decide) hp⟩⟩
  rw [(tab_ok hp).1]
  simp only [j1ta, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hp, Option.map_some, Option.getD_some]
  rw [CertificateChecks.KernelSpor.J1K.orb_eq.1]
  exact CertificateChecks.KernelSpor.J1K.al_get hp

theorem good_tb : Good 1540 j1tb.toArray (L 1) := by
  refine ⟨by simp [j1tb], fun p hp => ⟨?_, range_ok (by decide) hp⟩⟩
  rw [(tab_ok hp).2.1]
  simp only [j1tb, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hp, Option.map_some, Option.getD_some]
  rw [CertificateChecks.KernelSpor.J1K.orb_eq.1]
  exact CertificateChecks.KernelSpor.J1K.be_get hp

theorem good_ab : ∀ l < (#[j1ta.toArray, j1tb.toArray] : Array (Array ℕ)).size,
    Good 1540 ((#[j1ta.toArray, j1tb.toArray] : Array (Array ℕ)).getD l #[]) (L l)
  | 0, _ => good_ta
  | 1, _ => good_tb
  | _ + 2, h => absurd h (by simp)

theorem hel_ab : ∀ l < (#[(a : G), (b : G)] : Array G).size,
    (#[j1ta.toArray, j1tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 1540 ((#[(a : G), (b : G)] : Array G).getD l 1)).toArray
  | 0, _ => j1_tab_a.symm
  | 1, _ => j1_tab_b.symm
  | _ + 2, h => absurd h (by simp)

theorem good_wordElt {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good 1540 (tab 1540 (wordElt (a : G) (b : G) w)).toArray (wordF L w) := by
  unfold wordElt
  rw [← wordTabA_eq #[(a : G), (b : G)] _ hel_ab w (by simpa using hw)]
  exact good_word good_ab (by simpa using hw)

theorem j1Words_lt : ∀ w ∈ j1Words, ∀ l ∈ w, l < 2 := by decide

@[expose] noncomputable def sgK : List G := j1Words.map (wordElt (a : G) (b : G))

theorem sgK_get {i : ℕ} (hi : i < 3) :
    sgK.getD i 1 = wordElt (a : G) (b : G) (j1Words.getD i []) := by
  unfold sgK
  interval_cases i <;> rfl

theorem sgK_tabs : genTabs 1540 sgK = j1STabs := by
  unfold genTabs sgK j1STabs
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw'
  exact (wordTabA_eq #[(a : G), (b : G)] #[j1ta.toArray, j1tb.toArray] hel_ab w
    fun l hl => by simpa using j1Words_lt w hw' l hl).symm

theorem good_sg {i : ℕ} (hi : i < 3) : Good 1540 (tab 1540 (sgK.getD i 1)).toArray (L2 i) := by
  rw [sgK_get hi]
  refine good_congr (good_wordElt fun l hl => j1Words_lt _ ?_ l hl) fun p hp =>
    ((tab_ok hp).2.2 i hi).symm
  have : i < j1Words.length := by simpa [j1Words] using hi
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem this

theorem sgK_len : sgK.length = 3 := rfl

theorem good_sgA : ∀ l < (genTabs 1540 sgK).toArray.size,
    Good 1540 ((genTabs 1540 sgK).toArray.getD l #[]) (L2 l) := by
  intro l hl
  have hl' : l < 3 := by simpa [genTabs, sgK_len] using hl
  rw [genTabs_hel sgK l (by simpa [sgK_len] using hl')]
  have e : sgK.toArray.getD l 1 = sgK.getD l 1 := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e]
  exact good_sg hl'

@[expose] noncomputable def sElt (w : List ℕ) : G := evalElt sgK.toArray w

theorem good_sw {w : List ℕ} (hw : ∀ l ∈ w, l < 3) :
    Good 1540 (tab 1540 (sElt w)).toArray (wordF L2 w) := by
  unfold sElt
  rw [← wordTabA_eq sgK.toArray (genTabs 1540 sgK).toArray (genTabs_hel sgK) w
    (by simpa [sgK_len] using hw)]
  exact good_word good_sgA (by simpa [genTabs, sgK_len] using hw)

theorem sElt_mem {w : List ℕ} (hw : ∀ l ∈ w, l < 3) :
    sElt w ∈ Subgroup.closure {x | x ∈ sgK} := by
  refine evalElt_mem sgK.toArray (fun l hl => ?_) w (by simpa [sgK_len] using hw)
  apply Subgroup.subset_closure
  have hl' : l < sgK.length := by simpa using hl
  simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hl', List.getElem_mem hl']

theorem Sw_lt : ∀ w ∈ Sw, ∀ l ∈ w, l < 3 := by decide

theorem sgK_inv : ∀ g ∈ sgK, g⁻¹ = g := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi3 : i < 3 := by rwa [sgK_len] at hi
  rw [(List.getD_eq_getElem _ 1 hi).symm]
  apply inv_eq_of_mul_eq_one_right
  have h1 := good_mul' (good_sg hi3) (good_sg hi3)
  have h2 : Good 1540 (tab 1540 (1 : G)).toArray (fun p => p) := by
    refine ⟨by simp [tab], fun p hp => ⟨?_, hp⟩⟩
    have e := img_tab (n := 1540) (1 : G) p
    rw [img] at e
    rw [e, act_one hp]
  exact eq_of_maps h1 h2 fun p hp => (inv_ok hi3 hp).1

theorem sw_mul {i : ℕ} (hi : i < 3) {w : List ℕ} (hw : w ∈ Sw) :
    ∃ w' ∈ Sw, sgK.getD i 1 * sElt w = sElt w' := by
  have h := List.any_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 sClosedB i
    (List.mem_range.2 hi)) w hw)
  obtain ⟨w', hw', e⟩ := h
  refine ⟨w', hw', eq_of_maps (good_mul' (good_sg hi) (good_sw (Sw_lt w hw)))
    (good_sw (Sw_lt w' hw')) fun p hp => ?_⟩
  exact beq_iff_eq.1 (List.all_eq_true.1 e p (List.mem_range.2 hp))

theorem sw_nodup : (Sw.map sElt).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro x y hxy
  have hx : x.val < 8 := by simpa [Sw] using x.isLt
  have hy : y.val < 8 := by simpa [Sw] using y.isLt
  by_contra hne
  have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
  have h := List.all_eq_true.1 (List.all_eq_true.1 sDistinctB x.val (List.mem_range.2 hx)) y.val
    (List.mem_range.2 hy)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  rcases h with h | h
  · exact hne' (Nat.eq_of_beq_eq_true h)
  apply h
  have ex : (Sw.map sElt).get x = sElt (Sw.getD x.val []) := by
    rw [List.get_eq_getElem, List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa [Sw] using hx : x.val < Sw.length)]
  have ey : (Sw.map sElt).get y = sElt (Sw.getD y.val []) := by
    rw [List.get_eq_getElem, List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa [Sw] using hy : y.val < Sw.length)]
  rw [ex, ey] at hxy
  have hmx : Sw.getD x.val [] ∈ Sw := by
    rw [List.getD_eq_getElem _ _ (by simpa [Sw] using hx : x.val < Sw.length)]
    exact List.getElem_mem _
  have hmy : Sw.getD y.val [] ∈ Sw := by
    rw [List.getD_eq_getElem _ _ (by simpa [Sw] using hy : y.val < Sw.length)]
    exact List.getElem_mem _
  unfold sImg
  apply List.map_congr_left
  intro p hp
  have hp' := List.mem_range.1 hp
  rw [← (act_of_good (good_sw (Sw_lt _ hmx)) hp').1, ← (act_of_good (good_sw (Sw_lt _ hmy)) hp').1,
    hxy]

theorem j1K_card_S : Nat.card (Subgroup.closure {x | x ∈ sgK}) = 2 ^ 3 := by
  have h := card_closure_of_list sgK (Sw.map sElt) (List.mem_map.2 ⟨[], by decide, evalElt_nil _⟩)
    sgK_inv (fun g hg x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hi3 : i < 3 := by rwa [sgK_len] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      obtain ⟨w', hw', e⟩ := sw_mul hi3 hw
      rw [(List.getD_eq_getElem _ 1 hi).symm, e]
      exact List.mem_map_of_mem hw')
    (fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact sElt_mem (Sw_lt w hw)) sw_nodup
  rw [h]
  rfl

@[expose] noncomputable def sl : List G := sgK ++ sgK

theorem htake : sl.take 3 = sgK := by
  unfold sl
  rw [List.take_append_of_le_length (by rw [sgK_len]), List.take_of_length_le (by rw [sgK_len])]

theorem hL : ∀ l < 2 + C.ns,
    Good 1540 (tab 1540 (((a : G) :: (b : G) :: sl).getD l 1)).toArray (C.L l) := by
  intro l hl
  change l < 8 at hl
  change Good 1540 (tab 1540 (((a : G) :: (b : G) :: sl).getD l 1)).toArray (L l)
  rcases l with _ | _ | l
  · change Good 1540 (tab 1540 (a : G)).toArray (L 0)
    rw [j1_tab_a]
    exact good_ta
  · change Good 1540 (tab 1540 (b : G)).toArray (L 1)
    rw [j1_tab_b]
    exact good_tb
  · change Good 1540 (tab 1540 (sl.getD l 1)).toArray (L (l + 2))
    have hl' : l < 6 := by omega
    unfold sl
    rcases Nat.lt_or_ge l 3 with h3 | h3
    · rw [List.getD_append _ _ _ _ (by rw [sgK_len]; exact h3)]
      have e : L (l + 2) = L2 l := by rw [L2, Nat.add_comm]; rfl
      rw [e]
      exact good_sg h3
    · rw [List.getD_append_right _ _ _ _ (by rw [sgK_len]; exact h3), sgK_len]
      have hi : l - 3 < 3 := by omega
      refine good_congr (good_sg hi) fun p hp => ?_
      have e := (inv_ok hi hp).2
      rw [show Nat.add 5 (l - 3) = l + 2 by change 5 + (l - 3) = l + 2; omega] at e
      exact e.symm

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  apply Subgroup.subset_closure
  unfold sl at hx
  rcases List.mem_append.1 hx with h | h <;> exact h

theorem hsep : ∀ g : G, (∀ p ∈ D.sep, act 1540 g p = p) → g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact base_of_faithful g hg

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  have hl : D.Rc.length = 24 := rfl
  rw [hl, List.all_eq_true]
  intro i hi
  exact K.all i (List.mem_range.1 hi)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem deltaB : (J.delta == j1Delta) = true := by quickRfl

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_sound :
    (∀ g : G, lab 1540 ptLab C.Δ g = C.Δ ↔ g ∈ Subgroup.closure {x | x ∈ sl.take C.ng}) ∧
    ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take C.ng} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length
        (fun j => Subgroup.closure
          {x | x ∈ sl.take C.ng ++ (D.mw.getD j []).map (wordElt (a : G) (b : G))}) j :=
  @dcCheck_sound G _ _ 1540 _ C rfl D (a : G) (b : G) closure_ab sl
    (by simp [sl, sgK_len, C]) hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 3
        rw [htake]; exact j1K_card_S)
    (by change Nat.card G = 21945 * 2 ^ 3; rw [card_J]; norm_num) hsep
    (by change PtValid 1540 J.delta; rw [eq_of_beq deltaB]; exact j1_delta_valid) dc_ok

theorem j1K_stab : ∀ g : G, lab 1540 ptLab j1Delta g = j1Delta ↔
    g ∈ Subgroup.closure {x | x ∈ sgK} := by
  have h := dc_sound.1
  change ∀ g : G, lab 1540 ptLab J.delta g = J.delta ↔ g ∈ Subgroup.closure {x | x ∈ sl.take 3}
    at h
  rw [htake, eq_of_beq deltaB] at h
  exact h

theorem dc_complete : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sgK} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ sgK ++ (J.mw.getD j []).map (wordElt (a : G) (b : G))})
        j := by
  have h := dc_sound.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 3} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 3 ++ (D.mw.getD j []).map (wordElt (a : G) (b : G))}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.J1Dc

end
