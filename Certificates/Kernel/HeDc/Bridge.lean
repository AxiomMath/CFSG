module

public import Certificates.Kernel.HeDc.Glob
public import Certificates.Kernel.HeDc.C0
public import Certificates.Kernel.HeDc.C1
public import Certificates.Kernel.HeDc.C2
public import Certificates.Kernel.HeDc.C3
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import Certificates.Kernel.E68Spor4215.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HeDc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLOm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm

theorem ch_of {f : Nat → Bool} {o : Nat} (hf : ∀ i, f i = chunkOK C D (Nat.add o i))
    (h : ∀ i < 6, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + 6) : chunkOK C D i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem chunks_ok : (List.range D.Rc.length).all (chunkOK C D) = true := by
  have hl : D.Rc.length = 24 := rfl
  rw [hl, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  by_cases h0 : i < 6
  · exact ch_of (o := 0) (fun _ => rfl) K0.all (by omega) (by omega)
  by_cases h1 : i < 12
  · exact ch_of (o := 6) (fun _ => rfl) K1.all (by omega) (by omega)
  by_cases h2 : i < 18
  · exact ch_of (o := 12) (fun _ => rfl) K2.all (by omega) (by omega)
  · exact ch_of (o := 18) (fun _ => rfl) K3.all (by omega) (by omega)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks_ok]
  rfl

theorem he_ta : (tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)).toArray = heTa := by
  have : tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)
      CFSG.Sporadic.He.rep_alpha]
    simp [heTa, CFSG.Sporadic.He.orb]
  rw [this, Array.toArray_toList]

theorem he_tb : (tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)).toArray = heTb := by
  have : tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)
      CFSG.Sporadic.He.rep_beta]
    simp [heTb, CFSG.Sporadic.He.orb]
  rw [this, Array.toArray_toList]

theorem he_card : Nat.card CFSG.Sporadic.He.J = 2 ^ 10 * 3935925 := by
  rw [CFSG.Sporadic.He.card_J]; norm_num

@[expose] noncomputable def heSg : List CFSG.Sporadic.He.J :=
  heQp.map fun p => (slpElts CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg).getD p.1 1

theorem he_sGens : genTabs 8330 heSg = heSTabsC ∧
    Nat.card (Subgroup.closure {x | x ∈ heSg}) = 2 ^ 10 := by
  have hc : BaseCertS 8330 heB (slpTabsA (tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)).toArray
      (tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)).toArray heProg) heQp
      170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10 := by
    rw [he_ta, he_tb]
    exact he_cert
  have := sGens_of_baseCertS (n := 8330) heB he_base_lt he_base_property CFSG.Sporadic.He.a
    CFSG.Sporadic.He.b heProg he_valid heQp 170 249 253 251 255 heEnum.1 heEnum.2.1
    heEnum.2.2 10 hc
  refine ⟨?_, this.2⟩
  rw [heSg, this.1, he_ta, he_tb]
  rfl

@[irreducible] noncomputable def E (j : ℕ) : CFSG.Sporadic.He.J :=
  (slpElts CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg).getD j 1

theorem heSg_eq : heSg = [E 197, E 207, E 226, E 247] := by
  simp only [heSg, heQp, List.map_cons, List.map_nil, E]

@[expose] noncomputable def sl : List CFSG.Sporadic.He.J :=
  [E 197, E 207, E 226, E 247, E 256, E 262, E 263, E 266]

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem tab_node {j : ℕ} (hj : j < heProg.length + 2) :
    (tab 8330 ((slpElts CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg).getD j 1)).toArray =
      heSLP[j]! := by
  have hinv := slp_foldl_inv (n := 8330) heProg #[CFSG.Sporadic.He.a, CFSG.Sporadic.He.b]
    #[(tab 8330 CFSG.Sporadic.He.a).toArray, (tab 8330 CFSG.Sporadic.He.b).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using he_valid)
  have hs : j < (heProg.foldl slpStepA
      #[(tab 8330 CFSG.Sporadic.He.a).toArray, (tab 8330 CFSG.Sporadic.He.b).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : heProg.foldl slpStepA
      #[(tab 8330 CFSG.Sporadic.He.a).toArray, (tab 8330 CFSG.Sporadic.He.b).toArray] = heSLP := by
    rw [he_ta, he_tb]
    rfl
  rw [e2] at e
  unfold slpElts
  rw [e, Array.toArray_toList]

theorem good_node {j : ℕ} (hj : j < heProg.length + 2) :
    Good 8330 (tab 8330 (E j)).toArray (CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF j)) := by
  unfold E
  rw [tab_node hj]
  exact CFSG.KD.E68S4215.good_he hj

theorem good_L {l j : ℕ} (hl : nodes.getD l 0 = j) (hj : j < heProg.length + 2) :
    Good 8330 (tab 8330 (E j)).toArray (L l) := by
  have e : L l = CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF j) := by
    funext p
    unfold L
    rw [hl]
  rw [e]
  exact good_node hj

theorem good_a : Good 8330 heTa (L 0) := by
  have h := CFSG.KD.E68S4215.good_he (j := 0) (by decide)
  unfold heSLP at h
  rw [(CFSG.KD.E68S4215.slp_get01 heTa heTb heProg).1] at h
  exact h

theorem good_b : Good 8330 heTb (L 1) := by
  have h := CFSG.KD.E68S4215.good_he (j := 1) (by decide)
  unfold heSLP at h
  rw [(CFSG.KD.E68S4215.slp_get01 heTa heTb heProg).2] at h
  exact h

theorem hL : ∀ l < 2 + C.ns,
    Good 8330 (tab 8330 ((CFSG.Sporadic.He.a :: CFSG.Sporadic.He.b :: sl).getD l 1)).toArray
      (C.L l) := by
  intro l hl
  have hl' : l < 10 := hl
  interval_cases l
  · change Good 8330 (tab 8330 CFSG.Sporadic.He.a).toArray (L 0)
    rw [he_ta]
    exact good_a
  · change Good 8330 (tab 8330 CFSG.Sporadic.He.b).toArray (L 1)
    rw [he_tb]
    exact good_b
  · exact good_L (l := 2) (j := 197) rfl (by decide)
  · exact good_L (l := 3) (j := 207) rfl (by decide)
  · exact good_L (l := 4) (j := 226) rfl (by decide)
  · exact good_L (l := 5) (j := 247) rfl (by decide)
  · exact good_L (l := 6) (j := 256) rfl (by decide)
  · exact good_L (l := 7) (j := 262) rfl (by decide)
  · exact good_L (l := 8) (j := 263) rfl (by decide)
  · exact good_L (l := 9) (j := 266) rfl (by decide)

theorem act_of_good {x : CFSG.Sporadic.He.J} {f : ℕ → ℕ} (hx : Good 8330 (tab 8330 x).toArray f)
    {p : ℕ} (hp : p < 8330) : act 8330 x p = f p ∧ f p < 8330 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : CFSG.Sporadic.He.J} {f g : ℕ → ℕ}
    (hx : Good 8330 (tab 8330 x).toArray f) (hy : Good 8330 (tab 8330 y).toArray g)
    (h : ∀ p < 8330, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply he_base_property
  intro b hb
  have hb' := he_base_lt b hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact h b hb'

theorem htake : sl.take 4 = heSg := by
  rw [heSg_eq]
  rfl

theorem hinvL : ∀ i < 4, ∀ p < 8330, L (Nat.add 6 i) (L (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (all_range (all_range invs i hi) p hp)

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 4}
  rw [htake]
  have hg : ∀ y ∈ [E 197, E 207, E 226, E 247], y ∈ Subgroup.closure {x | x ∈ heSg} :=
    fun y hy => Subgroup.subset_closure (by rw [heSg_eq]; exact hy)
  have hm : ∀ i < 4, ∀ j k : ℕ, nodes.getD (Nat.add 2 i) 0 = j → j < heProg.length + 2 →
      nodes.getD (Nat.add 6 i) 0 = k → k < heProg.length + 2 →
      E j ∈ [E 197, E 207, E 226, E 247] → E k ∈ Subgroup.closure {x | x ∈ heSg} := by
    intro i hi j k e1 hj e2 hk hmem
    rw [eq_inv_of_maps (good_L e2 hk) (good_L e1 hj) (hinvL i hi)]
    exact Subgroup.inv_mem _ (hg _ hmem)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hm 0 (by decide) 197 256 rfl (by decide) rfl (by decide) (by simp)
  · exact hm 1 (by decide) 207 262 rfl (by decide) rfl (by decide) (by simp)
  · exact hm 2 (by decide) 226 263 rfl (by decide) rfl (by decide) (by simp)
  · exact hm 3 (by decide) 247 266 rfl (by decide) rfl (by decide) (by simp)

theorem base_eq : CFSG.Sporadic.He.Native.chainBase.toList = [0, 1, 3, 4, 2] := rfl

theorem sepB : (D.sep == [0, 1, 3, 4, 2]) = true := by quickRfl

theorem hsep : ∀ g : CFSG.Sporadic.He.J, (∀ p ∈ D.sep, act 8330 g p = p) → g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact he_base_property g (by rw [base_eq]; exact hg)

theorem hmwB : (D.mw == heMwLit.toList) = true := by quickRfl

theorem hmw : D.mw = heMwLit.toList := eq_of_beq hmwB

theorem mw_get (j : ℕ) : D.mw.getD j [] = heMwLit[j]! := by
  rw [hmw, List.getD_eq_getElem?_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]
  rfl

theorem dc_facts :
    (∀ g : CFSG.Sporadic.He.J, lab 8330 ptLab heDelta g = heDelta ↔
      g ∈ Subgroup.closure {x | x ∈ heSg}) ∧
    ∀ Z : Subgroup CFSG.Sporadic.He.J, Subgroup.closure {x | x ∈ heSg} ≤ Z → ∃ j ≤ 11,
      Z = memberOrTop 11 (fun j => Subgroup.closure {x | x ∈ heSg ++
        (heMwLit[j]!).map (wordElt CFSG.Sporadic.He.a CFSG.Sporadic.He.b)}) j := by
  have h := dcCheck_sound (Γ := CFSG.Sporadic.He.J) (n := 8330) C rfl D CFSG.Sporadic.He.a
    CFSG.Sporadic.He.b CFSG.Sporadic.He.closure_ab sl rfl hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 4}) = 2 ^ 10
        rw [htake]; exact he_sGens.2)
    (by change Nat.card CFSG.Sporadic.He.J = 3935925 * 2 ^ 10; rw [he_card, mul_comm]) hsep
    (by decide) dc_ok
  change (∀ g : CFSG.Sporadic.He.J, lab 8330 ptLab heDelta g = heDelta ↔
      g ∈ Subgroup.closure {x | x ∈ sl.take 4}) ∧
    ∀ Z : Subgroup CFSG.Sporadic.He.J, Subgroup.closure {x | x ∈ sl.take 4} ≤ Z →
      ∃ j ≤ D.mw.length, Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 4 ++ (D.mw.getD j []).map
          (wordElt CFSG.Sporadic.He.a CFSG.Sporadic.He.b)}) j at h
  rw [htake] at h
  have hlen : D.mw.length = 11 := by rw [hmw]; rfl
  refine ⟨h.1, fun Z hZ => ?_⟩
  obtain ⟨j, hj, hZj⟩ := h.2 Z hZ
  refine ⟨j, by omega, ?_⟩
  rw [hZj, hlen]
  simp only [mw_get]

end CFSG.KD.HeDc

end
