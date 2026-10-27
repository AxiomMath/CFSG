module

public import Certificates.Kernel.Misc.KGroups.U33AChecks
public import Certificates.Kernel.Misc.KGroups.U33PFacts

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33K

open Equiv CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT.P
open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

theorem A_eq : Subgroup.closure ({pa, pb, sg0} : Set (Perm (Fin 28))) =
    Subgroup.closure {g | g ∈ [pa, pb, sg0]} := by
  congr 1
  ext g
  simp

theorem treeAAll : ∀ k < 12096, treeAt (mul 28) (one 28) AG 3 EA PAA k = true :=
  forall_of_chunks 3024 4 _ fun c hc => by
    interval_cases c
    · exact treeA0
    · exact treeA1
    · exact treeA2
    · exact treeA3

theorem closedAAll : ∀ k < 12096, closedAt (mul 28) AG 3 12096 EA CTA k = true :=
  forall_of_chunks 3024 4 _ fun c hc => by
    interval_cases c
    · exact closedA0
    · exact closedA1
    · exact closedA2
    · exact closedA3

abbrev AA : Subgroup (Perm (Fin 28)) := Subgroup.closure {pa, pb, sg0}

theorem listA_proved : ExactList pcode AA 12096 EA := by
  have clos := clos_card_proved (pcode_enc_proved hn) [pa, pb, sg0] hA (by norm_num) treeAAll
    ((allN_iff _ _).1 sortAB)
  rw [AA, A_eq]
  exact ⟨clos.1, (clos.2.2 closedAAll).2, sort_distinct_proved ((allN_iff _ _).1 sortAB)⟩

theorem mem_of_inA_proved {g : Perm (Fin 28)} (h : inA (pcode g) = true) : g ∈ AA := by
  obtain ⟨j, hj, he⟩ := (anyN_iff _ _).1 h
  exact exact_mem_proved hn listA_proved hj (Nat.eq_of_beq_eq_true he).symm

theorem repF : (pt2 ∈ AA ∧ orderOf pt2 = 2) ∧ (px1 ∈ AA ∧ orderOf px1 = 3) ∧
    (px2 ∈ AA ∧ orderOf px2 = 3) := by
  obtain ⟨hA1, hA2⟩ := andB_iff.1 repB
  obtain ⟨h1, h2⟩ := andB_iff.1 hA1
  obtain ⟨hB1, hB2⟩ := andB_iff.1 hA2
  obtain ⟨h3, h4⟩ := andB_iff.1 hB1
  obtain ⟨h5, h6⟩ := andB_iff.1 hB2
  obtain ⟨e0, e1, e2⟩ := hR
  rw [← e0] at h1 h2
  rw [← e1] at h3 h4
  rw [← e2] at h5 h6
  exact ⟨⟨mem_of_inA_proved h1, (ordK_iff_proved hn _ (by norm_num)).1 h2⟩,
    ⟨mem_of_inA_proved h3, (ordK_iff_proved hn _ (by norm_num)).1 h4⟩,
    ⟨mem_of_inA_proved h5, (ordK_iff_proved hn _ (by norm_num)).1 h6⟩⟩

theorem c2AF : Nat.card {x // x ∈ AA ∧ orderOf x = 2} = 315 :=
  by
    have h := Nat.eq_of_beq_eq_true c2AB
    exact (cnt_ord_proved hn listA_proved (by norm_num)).symm.trans h

theorem cAuF : centCard AA pu = 192 :=
  by
    have h := Nat.eq_of_beq_eq_true cAuB
    exact (cnt_cent_proved hn listA_proved hGU).symm.trans h

theorem cAtF : centCard AA pt2 = 48 :=
  by
    have h := Nat.eq_of_beq_eq_true cAtB
    exact (cnt_cent_proved hn listA_proved hR.1).symm.trans h

theorem centAF : ∀ σ ∈ AA, σ * pu = pu * σ → σ * pv = pv * σ → σ = 1 :=
  cent_sound_proved hn listA_proved hGU hGV ((allN_iff _ _).1 centAB)

theorem e9uF : E9At AA pu := e9_sound_proved hn listA_proved hGU ((allN_iff _ _).1 inuB) e9uB

theorem e9tF : E9At AA pt2 := e9_sound_proved hn listA_proved hR.1 ((allN_iff _ _).1 intB) e9tB

theorem c3AF : Nat.card {x // x ∈ AA ∧ orderOf x = 3} = 728 :=
  by
    have h := Nat.eq_of_beq_eq_true c3AB
    exact (cnt_ord_proved hn listA_proved (by norm_num)).symm.trans h

theorem cA1F : centCard AA px1 = 216 :=
  by
    have h := Nat.eq_of_beq_eq_true cA1B
    exact (cnt_cent_proved hn listA_proved hR.2.1).symm.trans h

theorem cA2F : centCard AA px2 = 18 :=
  by
    have h := Nat.eq_of_beq_eq_true cA2B
    exact (cnt_cent_proved hn listA_proved hR.2.2).symm.trans h

theorem e27aF : E27At AA px1 :=
  e27_sound_proved hn listA_proved hR.2.1 ((allN_iff _ _).1 in1B) e27aB

theorem e27bF : E27At AA px2 :=
  e27_sound_proved hn listA_proved hR.2.2 ((allN_iff _ _).1 in2B) e27bB

theorem ordUV : orderOf pu = 2 ∧ orderOf pv = 7 ∧ PairInv wsU pu pv := by
  obtain ⟨h1, h2⟩ := andB_iff.1 ordUVB
  obtain ⟨h2, h3⟩ := andB_iff.1 h2
  rw [← hGU] at h1 h3
  rw [← hGV] at h2 h3
  exact ⟨(ordK_iff_proved hn _ (by norm_num)).1 h1, (ordK_iff_proved hn _ (by norm_num)).1 h2,
    (pairK_iff_proved hn _ _ wsU wsU_pos).1 h3⟩

end CertificateChecks.KernelMisc.U33K

end
