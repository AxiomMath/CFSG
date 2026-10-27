module

public import Certificates.Kernel.Misc.KGroups.U33PChecks
public import CFSG.Certificates.Kernel.Misc.KGrpProof

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33K

open Equiv CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT
open CFSG.KC.LQT.P CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

theorem hA : ∀ a < [pa, pb, sg0].length, AG a = pcode ([pa, pb, sg0].getD a 1) := by
  decide +kernel

theorem hU : ∀ a < [pu, pv].length, UG a = pcode ([pu, pv].getD a 1) := by
  decide +kernel

theorem hR : pcode pt2 = RG 0 ∧ pcode px1 = RG 1 ∧ pcode px2 = RG 2 := by
  decide +kernel

theorem hImg : ∀ k : Fin 5, inP (pcode (CFSG.Quasithin.u33Img k)) = true := by
  decide +kernel

theorem hn : 28 ≤ 32 := by norm_num

theorem P_eq : Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) =
    Subgroup.closure {g | g ∈ [pa, pb]} := by
  congr 1
  ext g
  simp

theorem hAP : ∀ a < [pa, pb].length, AG a = pcode ([pa, pb].getD a 1) := by
  intro a ha
  have ha2 : a < 2 := ha
  interval_cases a
  · exact hA 0 (by norm_num)
  · exact hA 1 (by norm_num)

theorem treePAll : ∀ k < 6048, treeAt (mul 28) (one 28) AG 2 EP PAP k = true :=
  forall_of_chunks 1512 4 _ fun c hc => by
    interval_cases c
    · exact treeP0
    · exact treeP1
    · exact treeP2
    · exact treeP3

theorem closedPAll : ∀ k < 6048, closedAt (mul 28) AG 2 6048 EP CTP k = true :=
  forall_of_chunks 1512 4 _ fun c hc => by
    interval_cases c
    · exact closedP0
    · exact closedP1
    · exact closedP2
    · exact closedP3

theorem listP_proved :
    ExactList pcode (Subgroup.closure ({pa, pb} : Set (Perm (Fin 28)))) 6048 EP := by
  have clos := clos_card_proved (pcode_enc_proved hn) [pa, pb] hAP (by norm_num) treePAll
    ((allN_iff _ _).1 sortPB)
  rw [P_eq]
  exact ⟨clos.1, (clos.2.2 closedPAll).2, sort_distinct_proved ((allN_iff _ _).1 sortPB)⟩

theorem mem_of_inP_proved {g : Perm (Fin 28)} (h : inP (pcode g) = true) :
    g ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) := by
  obtain ⟨j, hj, he⟩ := (anyN_iff _ _).1 h
  exact exact_mem_proved hn listP_proved hj (Nat.eq_of_beq_eq_true he).symm

theorem hGU : pcode pu = UG 0 := (hU 0 (by norm_num)).symm
theorem hGV : pcode pv = UG 1 := (hU 1 (by norm_num)).symm
theorem hGS : pcode sg0 = AG 2 := (hA 2 (by norm_num)).symm

theorem conj_code (g x : Perm (Fin 28)) :
    P.conj 28 (pcode g) (pcode x) = pcode (g * x * g⁻¹) := by
  rw [P.conj, pcode_mul_proved hn, pcode_inv_proved hn, pcode_mul_proved hn]

theorem memF : pu ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) ∧
    pv ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) ∧
    sg0 * pu * sg0⁻¹ ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) ∧
    sg0 * pv * sg0⁻¹ ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) := by
  obtain ⟨h1, h2⟩ := andB_iff.1 memB
  obtain ⟨h2, h3⟩ := andB_iff.1 h2
  obtain ⟨h3, h4⟩ := andB_iff.1 h3
  rw [← hGU] at h1
  rw [← hGV] at h2
  rw [← hGS, ← hGU, conj_code] at h3
  rw [← hGS, ← hGV, conj_code] at h4
  exact ⟨mem_of_inP_proved h1, mem_of_inP_proved h2, mem_of_inP_proved h3, mem_of_inP_proved h4⟩

theorem wordF : pa ∈ Subgroup.closure ({pu, pv} : Set (Perm (Fin 28))) ∧
    pb ∈ Subgroup.closure ({pu, pv} : Set (Perm (Fin 28))) := by
  have huv : Subgroup.closure ({pu, pv} : Set (Perm (Fin 28))) =
      Subgroup.closure {g | g ∈ [pu, pv]} := by
    congr 1
    ext g
    simp
  have key : ∀ j < 2, ([pa, pb].getD j 1) ∈ Subgroup.closure ({pu, pv} : Set (Perm (Fin 28))) := by
    intro j hj
    obtain ⟨h1, h2⟩ := andB_iff.1 ((allN_iff _ _).1 wordB j hj)
    obtain ⟨g, hg, hgc⟩ := word_mem_proved hn [pu, pv] hU h1
    have e : pcode g = pcode ([pa, pb].getD j 1) := by
      rw [hgc, show [pu, pv].length = 2 from rfl, Nat.eq_of_beq_eq_true h2, hAP j hj]
    rw [huv, ← (pcode_inj_proved hn).1 e]
    exact hg
  exact ⟨key 0 (by norm_num), key 1 (by norm_num)⟩

theorem imgF : ∀ k : Fin 5, CFSG.Quasithin.u33Img k ∈
    Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) := fun k => mem_of_inP_proved (hImg k)

theorem c2PF : Nat.card {x // x ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) ∧
    orderOf x = 2} = 63 :=
  (cnt_ord_proved hn listP_proved (by norm_num)).symm.trans (Nat.eq_of_beq_eq_true c2PB)

theorem wsU_pos : ∀ wk ∈ wsU, 0 < wk.2 := by
  intro wk hwk
  simp only [wsU, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rw [hwk]
  norm_num

theorem fibPE : cntN 6048 (fibAt 28 EP (UG 0) 7 wsU) = 192 := by
  have h := Nat.eq_of_beq_eq_true fibPB
  exact h

theorem fibPF : Nat.card {y // y ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 28))) ∧
    orderOf y = 7 ∧ PairInv wsU pu y} = 192 := by
  rw [← fib_card_proved hn listP_proved hGU (by norm_num) wsU_pos]
  exact fibPE

theorem cPuF : centCard (Subgroup.closure ({pa, pb} : Set (Perm (Fin 28)))) pu = 96 :=
  (cnt_cent_proved hn listP_proved hGU).symm.trans (Nat.eq_of_beq_eq_true cPuB)

theorem cPtF : centCard (Subgroup.closure ({pa, pb} : Set (Perm (Fin 28)))) pt2 = 24 :=
  (cnt_cent_proved hn listP_proved hR.1).symm.trans (Nat.eq_of_beq_eq_true cPtB)

end CertificateChecks.KernelMisc.U33K

end
