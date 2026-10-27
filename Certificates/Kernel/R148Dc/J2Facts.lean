module

public import Certificates.Kernel.R148Dc.J2Bridge
public import Certificates.Kernel.R148Dc.J2ClsChecks
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BJ2V
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Dc
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Block.TwoBTri

set_option maxRecDepth 100000

public section

namespace CFSG.KD.R148Dc.J2F

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLCls CFSG.KC.LQT.PW CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ)

theorem forall₂_mem {R : GJ → List ℕ → Prop} {gs : List GJ} {ws : List (List ℕ)}
    (h : List.Forall₂ R gs ws) : ∀ y ∈ gs, ∃ w ∈ ws, R y w := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨w, hw, h⟩ := ih y hy
      exact ⟨w, List.mem_cons_of_mem _ hw, h⟩

theorem forall₂_getD {R : GJ → List ℕ → Prop} {gs : List GJ} {ws : List (List ℕ)}
    (h : List.Forall₂ R gs ws) :
    gs.length = ws.length ∧ ∀ i < gs.length, R (gs.getD i 1) (ws.getD i []) := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    refine ⟨by simp [ih.1], fun i hi => ?_⟩
    rcases i with _ | i
    · exact hr
    · simpa using ih.2 i (by simpa using hi)

theorem act_of_good {g : GJ} {f : ℕ → ℕ} (h : Good 315 (tab 315 g).toArray f) {p : ℕ}
    (hp : p < 315) : act 315 g p = f p := by
  rw [← img_tab]
  exact (h.2 p hp).1

theorem eqOnN_spec {n : ℕ} {f g : ℕ → ℕ} (h : eqOnN n f g = true) {p : ℕ} (hp : p < n) :
    f p = g p := by
  simp only [eqOnN, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h p hp

theorem cls_sound {L : ℕ → ℕ → ℕ} {gs : List GJ} {ws : List (List ℕ)}
    (hg : List.Forall₂ (fun g w => Good 315 (tab 315 g).toArray (wordF L w)) gs ws)
    {x : GJ} {fx : ℕ → ℕ} (hx : Good 315 (tab 315 x).toArray fx) {cs : List ℕ}
    (h : clsOK L 315 fx ws cs = true) :
    ∃ S : Set GJ, x ∈ S ∧ Nat.card S ≤ 4 ∧
      ∀ y ∈ Subgroup.closure {g | g ∈ gs}, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
  unfold clsOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hne : cs ≠ [] := by
    rintro rfl
    exact absurd h1 (by decide)
  have hlen : cs.length ≤ 4 := of_decide_eq_true h2
  have hhead : cs.headD 0 ∈ cs := by
    obtain ⟨c, cs', rfl⟩ := List.exists_cons_of_ne_nil hne
    exact List.mem_cons_self
  refine ⟨{g | ∃ u ∈ cs, ∀ p < 315, act 315 g p = imgW 9 u p},
    ⟨cs.headD 0, hhead, fun p hp => by rw [act_of_good hx hp]; exact (eqOnN_spec h3 hp).symm⟩,
    ?_, ?_⟩
  · have hidx : ∀ g : {g : GJ | ∃ u ∈ cs, ∀ p < 315, act 315 g p = imgW 9 u p},
        ∃ i : Fin cs.length, ∀ p < 315, act 315 g.1 p = imgW 9 cs[i] p := by
      rintro ⟨g, u, hu, hr⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
      exact ⟨⟨i, hi⟩, hr⟩
    choose f hf using hidx
    have hinj : Function.Injective f := by
      intro g h e
      have h1 := hf g
      have h2 := hf h
      rw [e] at h1
      have hgh : ∀ p < 315, act 315 g.1 p = act 315 h.1 p := fun p hp =>
        (h1 p hp).trans (h2 p hp).symm
      have h3 := base_of_faithful (n := 315) (g.1⁻¹ * h.1) (fun b hb => by
        have hb' := List.mem_range.1 hb
        rw [act_mul _ _ hb', ← hgh b hb', ← act_mul _ _ hb', inv_mul_cancel, act_one hb'])
      exact Subtype.ext (inv_mul_eq_one.1 h3)
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_eq_fintype_card (α := Fin cs.length), Fintype.card_fin] at this
    omega
  · apply CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2.conj_closed_of_closure
    rintro y hy s ⟨u, hu, hs⟩
    obtain ⟨w, hw, hgood⟩ := forall₂_mem hg y hy
    obtain ⟨v, hv, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h4 w hw) u hu)
    refine ⟨v, hv, fun p hp => ?_⟩
    set q := act 315 y⁻¹ p with hqdef
    have hq : q < 315 := act_lt _ hp
    have hyq : act 315 y q = p := by
      rw [hqdef, ← act_mul _ _ hp, mul_inv_cancel, act_one hp]
    have hsq : imgW 9 u q < 315 := by rw [← hs _ hq]; exact act_lt _ hq
    have e1 : wordF L w (imgW 9 u q) = imgW 9 v (wordF L w q) := eqOnN_spec he hq
    rw [act_mul _ _ hp, ← hqdef, act_mul _ _ hq, hs _ hq, act_of_good hgood hsq, e1,
      ← act_of_good hgood hq, hyq]

theorem member_card {L : ℕ → ℕ → ℕ} {Δ : List ℕ} (hΔ : PtValid 315 Δ) {S : Subgroup GJ}
    (hstab : ∀ g : GJ, lab 315 ptLab Δ g = Δ ↔ g ∈ S) {gs : List GJ} {ws : List (List ℕ)}
    (hg : List.Forall₂ (fun g w => Good 315 (tab 315 g).toArray (wordF L w)) gs ws)
    (hS : S ≤ Subgroup.closure {g | g ∈ gs}) {O : OmegaData (List ℕ)}
    (hO : omOKG (fun l x => labF (wordF L (ws.getD l [])) x) Δ ws.length O = true) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = O.lbl.size * Nat.card S := by
  obtain ⟨hlen, hgi⟩ := forall₂_getD hg
  have hsz : (gs.toArray.map fun g => (tab 315 g).toArray).size = ws.length := by
    simp [hlen]
  have hget : ∀ l < (gs.toArray.map fun g => (tab 315 g).toArray).size,
      (gs.toArray.map fun g => (tab 315 g).toArray).getD l #[] = (tab 315 (gs.getD l 1)).toArray := by
    intro l hl
    have hl' : l < gs.length := by simpa using hl
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_eq_getElem hl', List.getD_eq_getElem _ _ hl']
    rfl
  have hG : ∀ l < (gs.toArray.map fun g => (tab 315 g).toArray).size,
      Good 315 ((gs.toArray.map fun g => (tab 315 g).toArray).getD l #[])
        (wordF L (ws.getD l [])) := fun l hl => by
    rw [hget l hl]
    exact hgi l (by simpa using hl)
  have hO' : OmegaSpec ptAct (gs.toArray.map fun g => (tab 315 g).toArray) Δ O :=
    J3K.om_spec (M := fun l => wordF L (ws.getD l [])) hG hΔ.2 (by rw [hsz]; exact hO)
  have hstab' : stab (ptLab_lawful (Γ := GJ) (n := 315)) hΔ = S := by
    ext g
    exact hstab g
  have hc := OmegaSpec.card_eq ptLab_lawful hΔ gs.toArray (by simp) (fun l hl => by
      rw [CFSG.KC.SLOm.getElem!_eq_getD', hget l hl, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        ← List.getD_eq_getElem?_getD]) hO'
    (H := Subgroup.closure {g | g ∈ gs}) (by rw [List.toList_toArray])
    (by rw [hstab']; exact hS)
  rw [hc, hstab']

theorem dvd_of_mod {s : ℕ} (h : (96 % s == 0) = true) : s * 36 ∣ 2 ^ 7 * 3 ^ 3 := by
  have h96 : s ∣ 96 := Nat.dvd_of_mod_eq_zero (by simpa using h)
  exact (Nat.mul_dvd_mul h96 (dvd_refl 36)).trans (by norm_num)

end CFSG.KD.R148Dc.J2F

namespace CFSG.KD.R148Dc.J2A

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLCls CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KD.R148Dc.J2 CFSG.KD.R148Dc.J2F
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ Ej)
open CFSG.ComponentClassification.J2Cover (pa pb)
open CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2 (VJ sgOf closure_sgOf card_E0_sup_VJ_eq)


theorem hL6 {l : ℕ} (hl : l < 6) :
    Good 315 (tab 315 ((pa :: pb :: sgA).getD l 1)).toArray (L l) := hL l hl

theorem card_S : Nat.card (Subgroup.closure {x | x ∈ sgA}) = 36 := by
  have e : sgA = sgOf 0 := rfl
  rw [e, closure_sgOf, card_E0_sup_VJ_eq (by norm_num)]

theorem good_wordElt {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good 315 (tab 315 (wordElt pa pb w)).toArray (wordF L w) := by
  have hel : ∀ l < (#[pa, pb] : Array GJ).size,
      (#[(tab 315 pa).toArray, (tab 315 pb).toArray] : Array (Array ℕ)).getD l #[] =
        (tab 315 ((#[pa, pb] : Array GJ).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l <;> rfl
  have e := wordTabA_eq #[pa, pb] _ hel w (by simpa using hw)
  change Good 315 (tab 315 (evalElt #[pa, pb] w)).toArray (wordF L w)
  rw [← e]
  refine good_word (fun l hl => ?_) (by simpa using hw)
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · exact hL6 (l := 0) (by norm_num)
  · exact hL6 (l := 1) (by norm_num)

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

theorem mw_len : J.mw.length = 9 := by
  have h := mwK
  rw [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem gensF (j : ℕ) : List.Forall₂ (fun g w => Good 315 (tab 315 g).toArray (wordF L w))
    (sgA ++ (J.mw.getD j []).map (wordElt pa pb)) (mE j) := by
  refine fa_append ?_ ?_
  · exact .cons (hL6 (l := 2) (by norm_num)) (.cons (hL6 (l := 3) (by norm_num))
      (.cons (hL6 (l := 4) (by norm_num)) (.cons (hL6 (l := 5) (by norm_num)) .nil)))
  · have key : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 2) →
        List.Forall₂ (fun g w => Good 315 (tab 315 g).toArray (wordF L w))
          (ws.map (wordElt pa pb)) ws := by
      intro ws hws
      induction ws with
      | nil => exact .nil
      | cons w ws ih =>
        exact .cons (good_wordElt (hws w List.mem_cons_self))
          (ih fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    exact key _ mw_lt

theorem lat_facts : ∀ Z : Subgroup GJ, Ej 0 ⊔ VJ 0 ≤ Z → Z = ⊤ ∨ Nat.card Z ∣ 2 ^ 7 * 3 ^ 3 ∨
    ∃ S : Set GJ, zJ ∈ S ∧ Nat.card S ≤ 4 ∧ ∀ y ∈ Z, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
  intro Z hZ
  obtain ⟨hstab, hcomp⟩ := dc_sound card_S
  have hS : Subgroup.closure {x | x ∈ sgA} ≤ Z := by
    have e : sgA = sgOf 0 := rfl
    rw [e, closure_sgOf]
    exact hZ
  obtain ⟨j, -, rfl⟩ := hcomp Z hS
  unfold memberOrTop
  split_ifs with hjl
  · right
    rw [mw_len] at hjl
    have hm := List.all_eq_true.1 memsK j (List.mem_range.2 hjl)
    unfold memK at hm
    rw [Bool.or_eq_true] at hm
    rcases hm with h96 | hcls
    · left
      have hc := member_card deltaV hstab (gensF j)
        (Subgroup.closure_mono fun x hx => List.mem_append_left _ hx)
        (List.all_eq_true.1 mems j (List.mem_range.2 hjl))
      rw [hc, card_S]
      exact dvd_of_mod h96
    · right
      exact cls_sound (gensF j) (hL6 (l := 2) (by norm_num)) hcls
  · left
    rfl

end CFSG.KD.R148Dc.J2A

namespace CFSG.KD.R148Dc.J2B

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLCls CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KD.R148Dc.J2 CFSG.KD.R148Dc.J2F
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ Ej)
open CFSG.ComponentClassification.J2Cover (pa pb)
open CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2 (VJ sgOf closure_sgOf card_E0_sup_VJ_eq)


theorem hL6 {l : ℕ} (hl : l < 6) :
    Good 315 (tab 315 ((pa :: pb :: sgB).getD l 1)).toArray (L l) := hL l hl

theorem card_S : Nat.card (Subgroup.closure {x | x ∈ sgB}) = 36 := by
  have e : sgB = sgOf 3 := rfl
  rw [e, closure_sgOf, card_E0_sup_VJ_eq (by norm_num)]

theorem good_wordElt {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good 315 (tab 315 (wordElt pa pb w)).toArray (wordF L w) := by
  have hel : ∀ l < (#[pa, pb] : Array GJ).size,
      (#[(tab 315 pa).toArray, (tab 315 pb).toArray] : Array (Array ℕ)).getD l #[] =
        (tab 315 ((#[pa, pb] : Array GJ).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l <;> rfl
  have e := wordTabA_eq #[pa, pb] _ hel w (by simpa using hw)
  change Good 315 (tab 315 (evalElt #[pa, pb] w)).toArray (wordF L w)
  rw [← e]
  refine good_word (fun l hl => ?_) (by simpa using hw)
  have hl' : l < 2 := by simpa using hl
  interval_cases l
  · exact hL6 (l := 0) (by norm_num)
  · exact hL6 (l := 1) (by norm_num)

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

theorem mw_len : J.mw.length = 12 := by
  have h := mwK
  rw [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem gensF (j : ℕ) : List.Forall₂ (fun g w => Good 315 (tab 315 g).toArray (wordF L w))
    (sgB ++ (J.mw.getD j []).map (wordElt pa pb)) (mE j) := by
  refine fa_append ?_ ?_
  · exact .cons (hL6 (l := 2) (by norm_num)) (.cons (hL6 (l := 3) (by norm_num))
      (.cons (hL6 (l := 4) (by norm_num)) (.cons (hL6 (l := 5) (by norm_num)) .nil)))
  · have key : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 2) →
        List.Forall₂ (fun g w => Good 315 (tab 315 g).toArray (wordF L w))
          (ws.map (wordElt pa pb)) ws := by
      intro ws hws
      induction ws with
      | nil => exact .nil
      | cons w ws ih =>
        exact .cons (good_wordElt (hws w List.mem_cons_self))
          (ih fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    exact key _ mw_lt

theorem lat_facts : ∀ Z : Subgroup GJ, Ej 0 ⊔ VJ 3 ≤ Z → Z = ⊤ ∨ Nat.card Z ∣ 2 ^ 7 * 3 ^ 3 ∨
    ∃ S : Set GJ, zJ ∈ S ∧ Nat.card S ≤ 4 ∧ ∀ y ∈ Z, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
  intro Z hZ
  obtain ⟨hstab, hcomp⟩ := dc_sound card_S
  have hS : Subgroup.closure {x | x ∈ sgB} ≤ Z := by
    have e : sgB = sgOf 3 := rfl
    rw [e, closure_sgOf]
    exact hZ
  obtain ⟨j, -, rfl⟩ := hcomp Z hS
  unfold memberOrTop
  split_ifs with hjl
  · right
    rw [mw_len] at hjl
    have hm := List.all_eq_true.1 memsK j (List.mem_range.2 hjl)
    unfold memK at hm
    rw [Bool.or_eq_true] at hm
    rcases hm with h96 | hcls
    · left
      have hc := member_card deltaV hstab (gensF j)
        (Subgroup.closure_mono fun x hx => List.mem_append_left _ hx)
        (List.all_eq_true.1 mems j (List.mem_range.2 hjl))
      rw [hc, card_S]
      exact dvd_of_mod h96
    · right
      exact cls_sound (gensF j) (hL6 (l := 2) (by norm_num)) hcls
  · left
    rfl

end CFSG.KD.R148Dc.J2B

end
