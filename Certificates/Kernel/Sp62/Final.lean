module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import Certificates.Kernel.Sp62.ChecksC
public import Certificates.Kernel.Sp62.ChecksO
public import Certificates.Kernel.Sp62.ChecksO3
public import Certificates.Kernel.Sp62.ChecksO4
public import Certificates.Kernel.Sp62.ChecksH

public section

namespace CFSG.KD.Sp62

open CFSG.KC.Sp62 CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

theorem pairs_ok : pairsCheck8036 = true := by
  have h1 : genP.all pairT = true := by decide +kernel
  have h2 : (List.finRange 3).all (fun i => pairT (zPair i)) = true := by decide +kernel
  have h3 : pairT tPair = true := by decide +kernel
  have h4 : (List.finRange 5).all (fun j => (centGens j).all pairT) = true := by decide +kernel
  unfold pairsCheck8036
  simp only [Bool.and_eq_true, List.all_eq_true] at h2 h4 ⊢
  rw [List.all_eq_true] at h1
  exact ⟨⟨⟨fun cc hc => pairCheck_of (h1 cc hc), fun i hi => pairCheck_of (h2 i hi)⟩,
    pairCheck_of h3⟩, fun j hj cc hc => pairCheck_of (h4 j hj cc hc)⟩


abbrev gs (j : Fin 5) : List (List ℕ) := (centGens j).map Prod.fst

theorem gs_len : ∀ j : Fin 5, (gs j).length = 2 := by decide

theorem gs_ok : ∀ j : Fin 5, ∀ s < 2, canon6 ((gs j).getD s []) = true ∧
    pk ((gs j).getD s []) = at2 REC (2 * (j : ℕ)) s := by decide +kernel

theorem gps_ok : ∀ s < 2, ∃ x y, gpsH.getD s [] = x ++ y ∧
    (canon6 x = true ∧ pk x = at2 REC 10 s) ∧ (canon6 y = true ∧ pk y = at2 REC 12 s)
  | 0, _ => ⟨aC, aI, rfl, by decide +kernel, by decide +kernel⟩
  | 1, _ => ⟨bC, bI, rfl, by decide +kernel, by decide +kernel⟩
  | s + 2, h => absurd h (by omega)

theorem zc_ok : ∀ i : Fin 3, canon6 (zCode i) = true := by decide +kernel

theorem a_ok : ∀ j : Fin 5, canon6 (vecCodeZ (aVec j)) = true ∧
    pk (vecCodeZ (aVec j)) = REC (33 + (j : ℕ)) := by
  have h : ∀ j : Fin 5, Nat.beq (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2))
      (aVec j 0).val (aVec j 1).val (aVec j 2).val) (REC (33 + (j : ℕ))) = true := by
    decide +kernel
  intro j
  obtain ⟨c, e⟩ := vecCode_pk zc_ok (aVec j 0).val (aVec j 1).val (aVec j 2).val
  exact ⟨c, e.trans (Nat.eq_of_beq_eq_true (h j))⟩

theorem b_ok : ∀ k : Fin 13, canon6 (vecCodeZ (hypB k)) = true ∧
    pk (vecCodeZ (hypB k)) = REC (14 + (k : ℕ)) := by
  have h : ∀ k : Fin 13, Nat.beq (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2))
      (hypB k 0).val (hypB k 1).val (hypB k 2).val) (REC (14 + (k : ℕ))) = true := by
    decide +kernel
  intro k
  obtain ⟨c, e⟩ := vecCode_pk zc_ok (hypB k 0).val (hypB k 1).val (hypB k 2).val
  exact ⟨c, e.trans (Nat.eq_of_beq_eq_true (h k))⟩

theorem z_ok : ∀ i : Fin 3, (canon6 (zPair i).1 = true ∧ pk (zPair i).1 = REC (27 + (i : ℕ))) ∧
    (canon6 (zPair i).2 = true ∧ pk (zPair i).2 = REC (30 + (i : ℕ))) := by
  have h : ∀ i : Fin 3, (Nat.beq (pk (zCode i)) (REC (27 + (i : ℕ))) &&
      Nat.beq (MULF (pk (zCode i)) (pk (zCode i))) (REC (30 + (i : ℕ)))) = true := by
    decide +kernel
  intro i
  have e := h i
  rw [Bool.and_eq_true] at e
  have m := mulE ⟨zc_ok i, rfl⟩ ⟨zc_ok i, rfl⟩
  exact ⟨⟨zc_ok i, Nat.eq_of_beq_eq_true e.1⟩, ⟨m.1, m.2.trans (Nat.eq_of_beq_eq_true e.2)⟩⟩

theorem wreath_ok : wreathCheck8036 = true := by
  have tc : canon6 tCode = true := by decide +kernel
  have tic : canon6 tCodeInv = true := by decide +kernel
  have w1 : ∀ i : Fin 3, (mul6 (mul6 (zCode i) (zCode i)) (zCode i) == one6) =
      Nat.beq (MULF (MULF (pk (zCode i)) (pk (zCode i))) (pk (zCode i))) ONE := fun i => by
    have m := mulE (mulE ⟨zc_ok i, rfl⟩ ⟨zc_ok i, rfl⟩) ⟨zc_ok i, rfl⟩
    rw [beq_pk m.1 canon6_one6, m.2, pk_one6]
  have w2 : ∀ i j : Fin 3, commutes6 (zCode i) (zCode j) =
      Nat.beq (MULF (pk (zCode i)) (pk (zCode j))) (MULF (pk (zCode j)) (pk (zCode i))) :=
    fun i j => by
      have m1 := mulE ⟨zc_ok i, rfl⟩ ⟨zc_ok j, rfl⟩
      have m2 := mulE ⟨zc_ok j, rfl⟩ ⟨zc_ok i, rfl⟩
      unfold commutes6
      rw [beq_pk m1.1 m2.1, m1.2, m2.2]
  have w3 : (mul6 (mul6 tCode tCode) tCode == one6) =
      Nat.beq (MULF (MULF (pk tCode) (pk tCode)) (pk tCode)) ONE := by
    have m := mulE (mulE ⟨tc, rfl⟩ ⟨tc, rfl⟩) ⟨tc, rfl⟩
    rw [beq_pk m.1 canon6_one6, m.2, pk_one6]
  have w4 : ∀ i : Fin 3, (conjStep6 (tCode ++ tCodeInv) (zCode i) == zCode (i + 1)) =
      Nat.beq (MULF (MULF (pk tCode) (pk (zCode i))) (pk tCodeInv)) (pk (zCode (i + 1))) :=
    fun i => by
      have m := conj_pk ⟨tc, rfl⟩ ⟨tic, rfl⟩ ⟨zc_ok i, rfl⟩
      rw [beq_pk m.1 (zc_ok (i + 1)), m.2]
  have w5 : ∀ a b c : ℕ, (vecCode a b c == one6) =
      Nat.beq (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b c) ONE := fun a b c => by
    have v := vecCode_pk zc_ok a b c
    rw [beq_pk v.1 canon6_one6, v.2, pk_one6]
  have w6 : ∀ a b c : ℕ, (vecCode a b c == tCode) =
      Nat.beq (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b c) (pk tCode) :=
    fun a b c => by
      have v := vecCode_pk zc_ok a b c
      rw [beq_pk v.1 tc, v.2]
  simp only [wreathCheck8036, w1, w2, w3, w4, w5, w6]
  decide +kernel

theorem comm_ok : ∀ j : Fin 5,
    (centGens j).all (fun cc => commutes6 cc.1 (vecCodeZ (aVec j))) = true := by
  have h : ∀ j : Fin 5, (centGens j).all (fun cc => canon6 cc.1 &&
      Nat.beq (MULF (pk cc.1) (REC (33 + (j : ℕ)))) (MULF (REC (33 + (j : ℕ))) (pk cc.1))) =
      true := by decide +kernel
  exact fun j => all_comm (a_ok j) (h j)

abbrev offC : Fin 5 → ℕ := ![38, 2199, 4360, 6521, 6630]

theorem clos_ok : ∀ j : Fin 5, closureOK (gs j) (closureT (gs j)) (centOrder j) = true ∧
    ∀ t < centOrder j, canon6 ((closureT (gs j)).getD t []) = true ∧
      pk ((closureT (gs j)).getD t []) = recX REC (offC j) t := by
  intro j
  fin_cases j
  · exact closure6_ok (gs_len 0) (by decide) (by decide) (gs_ok 0) tabC0_ok (by decide)
      (by decide) (by decide)
  · exact closure6_ok (gs_len 1) (by decide) (by decide) (gs_ok 1) tabC1_ok (by decide)
      (by decide) (by decide)
  · exact closure6_ok (gs_len 2) (by decide) (by decide) (gs_ok 2) tabC2_ok (by decide)
      (by decide) (by decide)
  · exact closure6_ok (gs_len 3) (by decide) (by decide) (gs_ok 3) tabC3_ok (by decide)
      (by decide) (by decide)
  · exact closure6_ok (gs_len 4) (by decide) (by decide) (gs_ok 4) tabC4_ok (by decide)
      (by decide) (by decide)

theorem orb_ok : ∀ j : Fin 5, orbitOK (orbitTable (vecCodeZ (aVec j))) (classSize j) = true := by
  intro j
  unfold orbitTable
  fin_cases j
  · exact orbit6_ok rfl (by decide) (by decide) gps_ok (a_ok 0) tabO0_ok (by decide) (by decide)
      (by decide)
  · exact orbit6_ok rfl (by decide) (by decide) gps_ok (a_ok 1) tabO1_ok (by decide) (by decide)
      (by decide)
  · exact orbit6_ok rfl (by decide) (by decide) gps_ok (a_ok 2) tabO2_ok (by decide) (by decide)
      (by decide)
  · exact orbit6_ok rfl (by decide) (by decide) gps_ok (a_ok 3) tabO3_ok (by decide) (by decide)
      (by decide)
  · exact orbit6_ok rfl (by decide) (by decide) gps_ok (a_ok 4) tabO4_ok (by decide) (by decide)
      (by decide)

theorem cent_ok : centCheck8036 = true := by
  unfold centCheck8036
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨comm_ok j, (clos_ok j).1⟩, orb_ok j⟩

theorem hyp_tab {j : Fin 5} {k : Fin 13} (hj : hypJ k = j) {bc hi : ℕ}
    (hb : canon6 (vecCodeZ (hypB k)) = true ∧ pk (vecCodeZ (hypB k)) = REC bc)
    (h : hypK REC bc (offC j) (centOrder j) hi = true) (hm : centOrder j ≤ 64 * hi) :
    allCheck (hypPred (vecCodeZ (hypB k))) (closureT (gs (hypJ k))) = true := by
  subst hj
  obtain ⟨hcl, hrec⟩ := clos_ok (hypJ k)
  have hsz : (closureT (gs (hypJ k))).size = centOrder (hypJ k) := by
    simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hcl
    exact hcl.1.1.1
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hsz] at ht
  have e := CFSG.KC.G2Three.allBelow_g2 h hm t ht
  rw [hypPred_eq hb (hrec t ht) (z_ok 0) (z_ok 1) (z_ok 2)]
  exact e

theorem hyp_ok : hypCheck8036 = true := by
  unfold hypCheck8036
  rw [List.all_eq_true]
  intro k _
  fin_cases k
  · exact hyp_tab (j := 0) rfl (b_ok _) hyp0_ok (by decide)
  · exact hyp_tab (j := 0) rfl (b_ok _) hyp1_ok (by decide)
  · exact hyp_tab (j := 0) rfl (b_ok _) hyp2_ok (by decide)
  · exact hyp_tab (j := 0) rfl (b_ok _) hyp3_ok (by decide)
  · exact hyp_tab (j := 1) rfl (b_ok _) hyp4_ok (by decide)
  · exact hyp_tab (j := 1) rfl (b_ok _) hyp5_ok (by decide)
  · exact hyp_tab (j := 1) rfl (b_ok _) hyp6_ok (by decide)
  · exact hyp_tab (j := 2) rfl (b_ok _) hyp7_ok (by decide)
  · exact hyp_tab (j := 4) rfl (b_ok _) hyp8_ok (by decide)
  · exact hyp_tab (j := 4) rfl (b_ok _) hyp9_ok (by decide)
  · exact hyp_tab (j := 2) rfl (b_ok _) hyp10_ok (by decide)
  · exact hyp_tab (j := 3) rfl (b_ok _) hyp11_ok (by decide)
  · exact hyp_tab (j := 3) rfl (b_ok _) hyp12_ok (by decide)

end CFSG.KD.Sp62

end
