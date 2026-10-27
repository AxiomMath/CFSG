
module

public import Certificates.Kernel.J2Dc.Checks
public import Certificates.Kernel.J2Dc.Nodes
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.Certificates.Kernel.SporLatDcLinSound
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Base
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.E2P.SporB.J2Lat
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PP CFSG.KC.LQT.BC CFSG.KC.LQT.PW

abbrev G : Type := ↥CFSG.Sporadic.J2.J

noncomputable abbrev ga : G := CFSG.Sporadic.J2.a

noncomputable abbrev gb : G := CFSG.Sporadic.J2.b

@[irreducible] noncomputable def E (j : ℕ) : G := (slpElts ga gb j2Prog).getD j 1

theorem tab_node {j : ℕ} (hj : j < j2Prog.length + 2) :
    (tab 315 (E j)).toArray = j2SLP[j]! := by
  have hinv := slp_foldl_inv (n := 315) j2Prog #[ga, gb]
    #[(tab 315 ga).toArray, (tab 315 gb).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using j2_valid)
  have hs : j < (j2Prog.foldl slpStepA #[(tab 315 ga).toArray, (tab 315 gb).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : j2Prog.foldl slpStepA #[(tab 315 ga).toArray, (tab 315 gb).toArray] = j2SLP := by
    rw [j2_ta', j2_tb']
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

@[expose] noncomputable def sl : List G := [E 155, E 166, E 179, E 191, E 192, E 193]

theorem good_node {j : ℕ} (hj : j < j2Prog.length + 2) :
    Good 315 (tab 315 (E j)).toArray (imgW 9 (nodeK R j)) := by
  have h := rep_good (rep_node hj)
  rw [← slp_lit] at h
  rw [tab_node hj]
  exact h

theorem good0 {l : ℕ} (hl : l < 8) :
    Good 315 (tab 315 ((ga :: gb :: sl).getD l 1)).toArray (L0 l) := by
  rw [L0_get]
  interval_cases l
  · change Good 315 (tab 315 ga).toArray _
    rw [j2_ta', CFSG.KD.LQT.C4142.ta_eq]
    exact rep_good (rep_codeK (by norm_num) tabLa)
  · change Good 315 (tab 315 gb).toArray _
    rw [j2_tb', CFSG.KD.LQT.C4142.tb_eq]
    exact rep_good (rep_codeK (by norm_num) tabLb)
  all_goals exact good_node (by decide)

theorem hL : ∀ l < 2 + C.ns,
    Good (315 * 315) (@tab G _ (315 * 315) (pairAction G 315)
      ((ga :: gb :: sl).getD l 1)).toArray (C.L l) :=
  fun l hl => good_pair (good0 (l := l) hl)

theorem tab_letter {l : ℕ} (hl : l < 8) :
    (tab 315 ((ga :: gb :: sl).getD l 1)).toArray = T l := by
  have hg := good0 hl
  have hc : J.tabs.getD l [] = (List.range 315).map (L0 l) :=
    eq_of_beq (List.all_eq_true.1 tabsC l (List.mem_range.2 hl))
  unfold T
  rw [hc]
  refine Array.ext (by rw [hg.1]; simp) fun i h1 _ => ?_
  have e := (hg.2 i (by rw [hg.1] at h1; exact h1)).1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some] at e
  rw [e]
  simp

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 315 (tab 315 x).toArray f) {p : ℕ}
    (hp : p < 315) : act 315 x p = f p ∧ f p < 315 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 315 (tab 315 x).toArray f)
    (hy : Good 315 (tab 315 y).toArray g) (h : ∀ p < 315, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := 315)
  intro b hb
  have hb' := List.mem_range.1 hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact h b hb'

@[expose] noncomputable def j2SgK : List G :=
  j2Qp.map fun p => (slpElts ga gb j2Prog).getD p.1 1

theorem j2SgK_eq : j2SgK = [E 155, E 166, E 179] := by
  simp only [j2SgK, j2Qp, List.map_cons, List.map_nil, E]

theorem j2K_sGens : genTabs 315 j2SgK = j2STabs ∧
    Nat.card (Subgroup.closure {x | x ∈ j2SgK}) = 2 ^ 7 := by
  have hc : BaseCertS 315 (List.range 315)
      (slpTabsA (tab 315 ga).toArray (tab 315 gb).toArray j2Prog) j2Qp
      143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 := by
    rw [j2_ta', j2_tb']
    exact j2_cert
  have := sGens_of_baseCertS (n := 315) (List.range 315) (fun b hb => List.mem_range.mp hb)
    base_of_faithful ga gb j2Prog j2_valid j2Qp 143 181 185 183 187 j2Enum.1
    j2Enum.2.1 j2Enum.2.2 7 hc
  refine ⟨?_, this.2⟩
  rw [j2SgK, this.1, j2_ta', j2_tb']
  rfl

theorem htake : sl.take 3 = j2SgK := by
  rw [j2SgK_eq]
  rfl

theorem hinvL : ∀ i < 3, ∀ p < 315, L0 (Nat.add 5 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 invs i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

theorem hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  have hg : ∀ y ∈ [E 155, E 166, E 179], y ∈ Subgroup.closure {x | x ∈ j2SgK} :=
    fun y hy => Subgroup.subset_closure (by rw [j2SgK_eq]; exact hy)
  have hm : ∀ i < 3, sl.getD (Nat.add 3 i) 1 =
      ((ga :: gb :: sl).getD (Nat.add 2 i) 1)⁻¹ := by
    intro i hi
    have e : sl.getD (Nat.add 3 i) 1 = (ga :: gb :: sl).getD (Nat.add 5 i) 1 := by
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
  · rw [show E 191 = ((ga :: gb :: sl).getD 2 1)⁻¹ from hm 0 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 192 = ((ga :: gb :: sl).getD 3 1)⁻¹ from hm 1 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 193 = ((ga :: gb :: sl).getD 4 1)⁻¹ from hm 2 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))

theorem sepB : (D.sep == (List.range 315).map (fun i => i + 315 * i)) = true := by quickRfl

theorem hsep : ∀ g : G, (∀ p ∈ D.sep, @act G _ (315 * 315) (pairAction G 315) g p = p) →
    g = 1 := by
  intro g hg
  rw [eq_of_beq sepB] at hg
  exact sep_pair base_of_faithful g hg

theorem dcL_ok : dcCheckL C D J.P = true := by
  unfold dcCheckL
  rw [glob, pts, orbs, osz, chunks]
  rfl

theorem dc_ok : dcCheck C D = true := dcCheck_of_dcCheckL dcL_ok

theorem hmwB : (D.mw == J.mw) = true := by quickRfl

theorem dc_complete : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ j2SgK} ≤ Z →
    ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
      (fun j => Subgroup.closure {x | x ∈ j2SgK ++ (J.mw.getD j []).map (wordElt ga gb)}) j := by
  have h := @dcCheck_sound G _ _ (315 * 315) (pairAction G 315) C rfl D ga gb
    CFSG.Sporadic.J2.closure_ab sl rfl hL hS
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 7
        rw [htake]; exact j2K_sGens.2)
    (by change Nat.card G = 4725 * 2 ^ 7; rw [CFSG.Sporadic.J2.card_J]; norm_num) hsep
    (by decide) dc_ok
  have h := h.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 3} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 3 ++ (D.mw.getD j []).map (wordElt ga gb)}) j at h
  rw [htake, eq_of_beq hmwB] at h
  exact h

end CFSG.KD.J2Dc

end
