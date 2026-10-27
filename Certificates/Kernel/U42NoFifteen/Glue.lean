module

public import Certificates.Kernel.U42NoFifteen.WChecks
public import Certificates.Kernel.QP45W.Glue
public import CFSG.Certificates.Kernel.ConjWalkSound
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvU42Check
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.KD.U42NF

open CFSG.KC.ConjWalk CFSG.KC.ConjCount CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.KGroups.Native CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.U42
  CFSG.QuasithinUnique.K1.SporadicPerm


theorem closure_eq : QP45.originalSubgroup = Subgroup.closure {g | g ∈ [x45, y45]} := by
  rw [Certificates.Kernel.QP45W.orig_eq, tab_eq, tab_eq]

theorem t_eq : t = [x45, y45].map (tab 45) := eq_of_beq ch26122w_tabs

theorem t0_eq : t.getD 0 [] = tab 45 x45 := by
  rw [t_eq, List.map_cons, List.getD_cons_zero]

theorem t1_eq : t.getD 1 [] = tab 45 y45 := by
  rw [t_eq, List.map_cons, List.map_cons, List.getD_cons_succ, List.getD_cons_zero]

theorem ti0_eq : ti.getD 0 [] = tab 45 x45⁻¹ := by
  have h := ch26122w_inv
  rw [Bool.and_eq_true, t0_eq] at h
  exact inv_of_invOK h.1

theorem ti1_eq : ti.getD 1 [] = tab 45 y45⁻¹ := by
  have h := ch26122w_inv
  rw [Bool.and_eq_true, t1_eq] at h
  exact inv_of_invOK h.2

theorem y45_order : orderOf y45 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := ch26122w_ord
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  have hw : ∀ w : List ℕ, (∀ l ∈ w, l = 1) → ∀ l ∈ w, l < [x45, y45].length := by
    intro w hw l hl
    rw [hw l hl]
    simp
  have e5 := tabW_eq t_eq [1, 1, 1, 1, 1] (hw _ (by simp))
  have e1 := tabW_eq t_eq [1] (hw _ (by simp))
  have v5 : evalL [x45, y45] [1, 1, 1, 1, 1] = y45 ^ 5 := by
    simp only [evalL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.getD_cons_succ, List.getD_cons_zero, mul_one]
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  have v1 : evalL [x45, y45] [1] = y45 := by
    simp only [evalL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.getD_cons_succ, List.getD_cons_zero, mul_one]
  rw [v5] at e5
  rw [v1] at e1
  refine orderOf_eq_prime (eq_of_tab (n := 45) ?_) fun hy => h.2 ?_
  · rw [← e5, h.1, tab_one_eq]
  · rw [e1, hy, tab_one_eq]

theorem noFifteen : ∀ z ∈ QP45.originalSubgroup, orderOf z ≠ 15 := by
  have hc : Nat.card (Subgroup.closure {g | g ∈ [x45, y45]}) = 5 * 5184 := by
    rw [← closure_eq, card_group QP45 QP45_ok, QP45_valid.2]
  have hx : x45 ∈ Subgroup.closure {g | g ∈ [x45, y45]} := Subgroup.subset_closure (by simp)
  have hy : y45 ∈ Subgroup.closure {g | g ∈ [x45, y45]} := Subgroup.subset_closure (by simp)
  rw [closure_eq]
  refine walkK_noFifteen (n := 45) hx hy ?_ ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num)
    ch26122w hy y45_order hc (by norm_num) (by rw [hc, ch26122w_len]; norm_num)
  · rw [t0_eq]; exact rp_encL (by norm_num) x45
  · rw [ti0_eq]; exact rp_encL (by norm_num) x45⁻¹
  · rw [t1_eq]; exact rp_encL (by norm_num) y45
  · rw [ti1_eq]; exact rp_encL (by norm_num) y45⁻¹
  · rw [t1_eq]; exact rp_encL (by norm_num) y45

theorem check : u42NoFifteenCheck = true := by
  unfold u42NoFifteenCheck noElemOrderCheck
  rw [enumA_eq, List.all_map, List.all_eq_true]
  intro y hy
  have hm := (mem_elemsT QP45 QP45_ok y).1 hy
  simp only [Function.comp_apply, Bool.not_eq_true']
  rw [orderIsA_rep (rep_toA y) 15]
  cases e : orderIs y 15
  · rfl
  · exact absurd ((orderIs_iff y (by norm_num)).1 e) (noFifteen y hm)

end CFSG.KD.U42NF

end
