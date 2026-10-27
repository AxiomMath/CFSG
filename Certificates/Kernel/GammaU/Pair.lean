
module

public import Certificates.Kernel.GammaU.PairOK
public import Certificates.Kernel.GammaU.Triple
public import CFSG.Certificates.Kernel.GammaUPairSound

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUPB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem n2_le {i : Nat} (hrows : ((ResPair.n2Gens i).all fun r => rowsOK r.toList) = true)
    {M : Subgroup GL}
    (hM : ∀ q < (ResPair.n2Gens i).length, ∀ V,
      IsP V (nthD 0 ((ResPair.n2Gens i).map packR) q) → V ∈ M) : ResPair.n2 i ≤ M := by
  rw [ResPair.n2, Viol.genGrp, Subgroup.closure_le]
  rintro V ⟨r, hr, hVr⟩
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hr
  refine hM q hq V ?_
  rw [nthD_map _ _ _ #[] hq, getD_of_lt _ hq]
  exact (isP_packR (List.all_eq_true.1 hrows _ hr) V).2 hVr

theorem rc_rows {i j : Nat} (hrows : ((ResPair.resConj i).all fun r => rowsOK r.toList) = true)
    (hj : j < (ResPair.resConj i).length) {U : GL}
    (hU : IsP U (nthD 0 ((ResPair.resConj i).map packR) j)) :
    ∀ v, U v = linOfRows ((ResPair.resConj i).getD j #[]) v := by
  rw [nthD_map _ _ _ #[] hj] at hU
  have hmem : (ResPair.resConj i).getD j #[] ∈ ResPair.resConj i := by
    rw [getD_of_lt _ hj]
    exact List.getElem_mem hj
  exact (isP_packR (List.all_eq_true.1 hrows _ hmem) U).1 hU

theorem candL_same {CG FT FTi FC TH i X Y : Nat} {l : Nat} (hl : l < 11) (h : ¬ (5 ≤ l ∧ l < 10)) :
    candL CG FT FTi FC TH i Y l = candL CG FT FTi FC TH i X l := by
  unfold candL
  by_cases h5 : l < 5
  · rw [blt_t h5, cond_true, cond_true]
  · rw [blt_f h5, cond_false, cond_false, blt_f (by omega : ¬ l < 10), cond_false, cond_false]

theorem div_six {k d : Nat} (hd : d < 6) : Nat.div (6 * k + d) 6 = k := by
  change (6 * k + d) / 6 = k
  omega

theorem mod_six {k d : Nat} (hd : d < 6) : Nat.mod (6 * k + d) 6 = d := by
  change (6 * k + d) % 6 = d
  omega

theorem div_two {k d : Nat} (hd : d < 2) : Nat.div (2 * k + d) 2 = k := by
  change (2 * k + d) / 2 = k
  omega

theorem mod_two {k d : Nat} (hd : d < 2) : Nat.mod (2 * k + d) 2 = d := by
  change (2 * k + d) % 2 = d
  omega

end CFSG.KD.GUPB

namespace CFSG.KD.GUP0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS CFSG.KD.GUTB CFSG.KD.GUPB
open CFSG.KD.GUT0 (L NLG NLGI N2 NN XA ct16966a_inv ct16966a_n2)
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem lists_spec : PM.length = 4 ∧ RP.length = 6 ∧ (∀ d ∈ RP, d < 12) ∧ DR.length = 12 ∧
    RCI.length = RC.length ∧
    ∀ x < 12, fld CFSG.KD.GUC0.LB (nthD 0 XA x) = CFSG.KD.GUC0.AR := by
  have h := cp16966a_lists
  unfold lists at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff, allBelow_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h7, h8⟩

theorem conj_spec {j : Nat} (hj : j < 4) :
    ∃ C : GL, IsP C (look PC j) ∧ IsP C⁻¹ (look PCi j) ∧ C ∈ lGrp NLG 3 ∧
      mulP (subQ L (nthD 0 PM j)) (look PC j) = mulP (look PC j) CFSG.KD.GUC0.S0 := by
  have hcj := (allBelow_iff _ _).1 cp16966a_pcj j hj
  unfold pcj at hcj
  simp only [Bool.and_eq_true, Nat.beq_eq] at hcj
  obtain ⟨⟨⟨hw, hCW⟩, -⟩, hcjOK⟩ := hcj
  obtain ⟨C, hCm, hC⟩ := isP_wordP ct16966a_inv _ hw
  rw [hCW] at hC
  unfold CFSG.KC.GUV.cjOK at hcjOK
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hcjOK
  exact ⟨C, hC, hC.inv hcjOK.1, hCm, hcjOK.2⟩

theorem xa_lt {x : Nat} (hx : x < 12) : nthD 0 XA x < 384 :=
  CFSG.KD.GUT0.lists_spec.2.2.1 _ (nthD_mem 0 (by rw [CFSG.KD.GUT0.lists_spec.2.1]; exact hx))

theorem cand_mem {x : Nat} (hx : x < 12) :
    ∀ l < 11, ∃ V ∈ confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA
      (nthD 0 XA x), IsP V (cand x l) :=
  candL_mem CFSG.KD.GUCB.exists_isP_cg (by norm_num) (CFSG.KD.GUC0.len_spec.2.2.2 _ (xa_lt hx))
    (CFSG.KD.GUC0.isP_TX (xa_lt hx))
    ((CFSG.KD.GUC0.isP_TX (xa_lt hx)).inv (CFSG.KD.GUC0.inv_spec.1 _ (xa_lt hx)))
    CFSG.KD.GUC0.isP_θA

theorem cand_le {x : Nat} (hx : x < 12) {M : Subgroup GL}
    (hM : ∀ l < 11, ∀ V, IsP V (cand x l) → V ∈ M) :
    confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA (nthD 0 XA x) ≤ M :=
  confR_le (CFSG.KD.GUC0.isP_TX (xa_lt hx))
    ((CFSG.KD.GUC0.isP_TX (xa_lt hx)).inv (CFSG.KD.GUC0.inv_spec.1 _ (xa_lt hx)))
    CFSG.KD.GUC0.isP_θA hM

theorem card_xa {x : Nat} (hx : x < 12) :
    Nat.card (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA
      (nthD 0 XA x)) = 1152 :=
  ((CFSG.KD.GUC0.census_s0 _ (xa_lt hx)).1).2 (lists_spec.2.2.2.2.2 x hx)

theorem dr_spec {x : Nat} (hx : x < 12) : nthD 0 DR x < 6 ∧ nthD 0 RP (nthD 0 DR x) < 12 := by
  have hd := (allBelow_iff _ _).1 cp16966a_dup x hx
  unfold dup at hd
  rw [Bool.and_eq_true, Nat.blt_eq] at hd
  exact ⟨hd.1, lists_spec.2.2.1 _ (nthD_mem 0 (by rw [lists_spec.2.1]; exact hd.1))⟩

theorem grp_eq {x : Nat} (hx : x < 12) :
    confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA (nthD 0 XA x) =
      confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA
        (nthD 0 XA (nthD 0 RP (nthD 0 DR x))) := by
  have hd := (allBelow_iff _ _).1 cp16966a_dup x hx
  unfold dup at hd
  rw [Bool.and_eq_true] at hd
  have hr := (dr_spec hx).2
  have hle := dupOK_le hd.2 (fun l hl hn => candL_same hl hn) (cand_mem hr)
    (fun M hM => cand_le hx hM)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_xa hx, card_xa hr])

theorem n2_mem : ∀ e < NN, ∃ U ∈ ResPair.n2 0, IsP U (nthD 0 N2 e) := by
  intro e he
  rw [ct16966a_n2]
  refine n2_isP CFSG.KD.GUS0.cs16981a_rows CFSG.KD.GUS0.cs16981a_inv e ?_
  rw [CFSG.KD.GUT0.lists_spec.2.2.2.2.1, ct16966a_n2, List.length_map] at he
  exact he

theorem n2_le' {M : Subgroup GL} (hM : ∀ q < NN, ∀ V, IsP V (nthD 0 N2 q) → V ∈ M) :
    ResPair.n2 0 ≤ M :=
  n2_le CFSG.KD.GUS0.cs16981a_rows fun q hq V hV => hM q (by
    rw [CFSG.KD.GUT0.lists_spec.2.2.2.2.1, ct16966a_n2, List.length_map]; exact hq) V
    (by rw [ct16966a_n2]; exact hV)

theorem pair_s0 {k x₁ x₂ : Nat} (hk : k < 2) (hx₁ : x₁ < 12) (hx₂ : x₂ < 12) :
    ∃ C₁ C₂ : GL, IsP C₁ (look PC (2 * k)) ∧ IsP C₂ (look PC (2 * k + 1)) ∧
      C₁ ∈ lGrp NLG 3 ∧ C₂ ∈ lGrp NLG 3 ∧
      mulP (subQ L (nthD 0 PM (2 * k))) (look PC (2 * k)) =
        mulP (look PC (2 * k)) CFSG.KD.GUC0.S0 ∧
      mulP (subQ L (nthD 0 PM (2 * k + 1))) (look PC (2 * k + 1)) =
        mulP (look PC (2 * k + 1)) CFSG.KD.GUC0.S0 ∧
      (Viol.Violation (pairG
          (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA (nthD 0 XA x₁))
          (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA (nthD 0 XA x₂))
          C₁ C₂) (compOf 0) (compOf 0) ∨
        ∃ j < (ResPair.resConj 0).length, ∃ U : GL,
          (∀ v, U v = linOfRows ((ResPair.resConj 0).getD j #[]) v) ∧
          pairG
            (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA
              (nthD 0 XA x₁))
            (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA
              (nthD 0 XA x₂)) C₁ C₂ = (ResPair.n2 0).map (MulAut.conj U).toMonoidHom) := by
  obtain ⟨C₁, hC₁, hC₁i, hC₁m, hs₁⟩ := conj_spec (j := 2 * k) (by omega)
  obtain ⟨C₂, hC₂, hC₂i, hC₂m, hs₂⟩ := conj_spec (j := 2 * k + 1) (by omega)
  refine ⟨C₁, C₂, hC₁, hC₂, hC₁m, hC₂m, hs₁, hs₂, ?_⟩
  obtain ⟨hd₁, hr₁⟩ := dr_spec hx₁
  obtain ⟨hd₂, hr₂⟩ := dr_spec hx₂
  rw [grp_eq hx₁, grp_eq hx₂]
  have hrow := cp16966a_all (6 * k + nthD 0 DR x₁) (by
    change 6 * k + nthD 0 DR x₁ < 12
    omega)
  unfold row at hrow
  rw [div_six hd₁, mod_six hd₁] at hrow
  have hp := (allBelow_iff _ _).1 hrow _ hd₂
  unfold pair letQ at hp
  have hL := (compOf_iff (c := 0) (by norm_num)).1
  have hL' := (compOf_iff (c := 0) (by norm_num)).2
  rcases pairW_spec hp (cand_mem hr₁) (cand_mem hr₂) (fun M hM => cand_le hr₁ hM)
      (fun M hM => cand_le hr₂ hM) rfl rfl hC₁ hC₁i hC₂ hC₂i linP_TH hL hL' n2_mem
      (fun M hM => n2_le' hM) with hv | ⟨j, hj, U, hU, heq⟩
  · exact Or.inl hv
  · have hj' : j < (ResPair.resConj 0).length := by
      rw [cp16966a_rc, List.length_map] at hj
      exact hj
    rw [cp16966a_rc] at hU
    exact Or.inr ⟨j, hj', U, rc_rows cp16966a_rcrows hj' hU, heq⟩

end CFSG.KD.GUP0

namespace CFSG.KD.GUP1

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS CFSG.KD.GUTB CFSG.KD.GUPB
open CFSG.KD.GUT1 (L NLG NLGI N2 NN XA ct16966b_inv ct16966b_n2)
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem lists_spec : PM.length = 4 ∧ RP.length = 2 ∧ (∀ d ∈ RP, d < 4) ∧ DR.length = 4 ∧
    RCI.length = RC.length ∧
    ∀ x < 4, fld CFSG.KD.GUC1.LB (nthD 0 XA x) = CFSG.KD.GUC1.AR := by
  have h := cp16966b_lists
  unfold lists at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff, allBelow_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h7, h8⟩

theorem conj_spec {j : Nat} (hj : j < 4) :
    ∃ C : GL, IsP C (look PC j) ∧ IsP C⁻¹ (look PCi j) ∧ C ∈ lGrp NLG 3 ∧
      mulP (subQ L (nthD 0 PM j)) (look PC j) = mulP (look PC j) CFSG.KD.GUC1.S0 := by
  have hcj := (allBelow_iff _ _).1 cp16966b_pcj j hj
  unfold pcj at hcj
  simp only [Bool.and_eq_true, Nat.beq_eq] at hcj
  obtain ⟨⟨⟨hw, hCW⟩, -⟩, hcjOK⟩ := hcj
  obtain ⟨C, hCm, hC⟩ := isP_wordP ct16966b_inv _ hw
  rw [hCW] at hC
  unfold CFSG.KC.GUV.cjOK at hcjOK
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hcjOK
  exact ⟨C, hC, hC.inv hcjOK.1, hCm, hcjOK.2⟩

theorem xa_lt {x : Nat} (hx : x < 4) : nthD 0 XA x < 384 :=
  CFSG.KD.GUT1.lists_spec.2.2.1 _ (nthD_mem 0 (by rw [CFSG.KD.GUT1.lists_spec.2.1]; exact hx))

theorem cand_mem {x : Nat} (hx : x < 4) :
    ∀ l < 11, ∃ V ∈ confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA
      (nthD 0 XA x), IsP V (cand x l) :=
  candL_mem CFSG.KD.GUC1.exists_isP_cg (by norm_num) (CFSG.KD.GUC1.len_spec.2.2.2 _ (xa_lt hx))
    (CFSG.KD.GUC1.isP_TX (xa_lt hx))
    ((CFSG.KD.GUC1.isP_TX (xa_lt hx)).inv (CFSG.KD.GUC1.inv_spec.1 _ (xa_lt hx)))
    CFSG.KD.GUC1.isP_θA

theorem cand_le {x : Nat} (hx : x < 4) {M : Subgroup GL}
    (hM : ∀ l < 11, ∀ V, IsP V (cand x l) → V ∈ M) :
    confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA (nthD 0 XA x) ≤ M :=
  confR_le (CFSG.KD.GUC1.isP_TX (xa_lt hx))
    ((CFSG.KD.GUC1.isP_TX (xa_lt hx)).inv (CFSG.KD.GUC1.inv_spec.1 _ (xa_lt hx)))
    CFSG.KD.GUC1.isP_θA hM

theorem card_xa {x : Nat} (hx : x < 4) :
    Nat.card (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA
      (nthD 0 XA x)) = 1152 :=
  ((CFSG.KD.GUC1.census_s0 _ (xa_lt hx)).1).2 (lists_spec.2.2.2.2.2 x hx)

theorem dr_spec {x : Nat} (hx : x < 4) : nthD 0 DR x < 2 ∧ nthD 0 RP (nthD 0 DR x) < 4 := by
  have hd := (allBelow_iff _ _).1 cp16966b_dup x hx
  unfold dup at hd
  rw [Bool.and_eq_true, Nat.blt_eq] at hd
  exact ⟨hd.1, lists_spec.2.2.1 _ (nthD_mem 0 (by rw [lists_spec.2.1]; exact hd.1))⟩

theorem grp_eq {x : Nat} (hx : x < 4) :
    confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA (nthD 0 XA x) =
      confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA
        (nthD 0 XA (nthD 0 RP (nthD 0 DR x))) := by
  have hd := (allBelow_iff _ _).1 cp16966b_dup x hx
  unfold dup at hd
  rw [Bool.and_eq_true] at hd
  have hr := (dr_spec hx).2
  have hle := dupOK_le hd.2 (fun l hl hn => candL_same hl hn) (cand_mem hr)
    (fun M hM => cand_le hx hM)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_xa hx, card_xa hr])

theorem n2_mem : ∀ e < NN, ∃ U ∈ ResPair.n2 1, IsP U (nthD 0 N2 e) := by
  intro e he
  rw [ct16966b_n2]
  refine n2_isP CFSG.KD.GUS1.cs16981b_rows CFSG.KD.GUS1.cs16981b_inv e ?_
  rw [CFSG.KD.GUT1.lists_spec.2.2.2.2.1, ct16966b_n2, List.length_map] at he
  exact he

theorem n2_le' {M : Subgroup GL} (hM : ∀ q < NN, ∀ V, IsP V (nthD 0 N2 q) → V ∈ M) :
    ResPair.n2 1 ≤ M :=
  n2_le CFSG.KD.GUS1.cs16981b_rows fun q hq V hV => hM q (by
    rw [CFSG.KD.GUT1.lists_spec.2.2.2.2.1, ct16966b_n2, List.length_map]; exact hq) V
    (by rw [ct16966b_n2]; exact hV)

theorem pair_s0 {k x₁ x₂ : Nat} (hk : k < 2) (hx₁ : x₁ < 4) (hx₂ : x₂ < 4) :
    ∃ C₁ C₂ : GL, IsP C₁ (look PC (2 * k)) ∧ IsP C₂ (look PC (2 * k + 1)) ∧
      C₁ ∈ lGrp NLG 3 ∧ C₂ ∈ lGrp NLG 3 ∧
      mulP (subQ L (nthD 0 PM (2 * k))) (look PC (2 * k)) =
        mulP (look PC (2 * k)) CFSG.KD.GUC1.S0 ∧
      mulP (subQ L (nthD 0 PM (2 * k + 1))) (look PC (2 * k + 1)) =
        mulP (look PC (2 * k + 1)) CFSG.KD.GUC1.S0 ∧
      (Viol.Violation (pairG
          (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA (nthD 0 XA x₁))
          (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA (nthD 0 XA x₂))
          C₁ C₂) (compOf 1) (compOf 1) ∨
        ∃ j < (ResPair.resConj 1).length, ∃ U : GL,
          (∀ v, U v = linOfRows ((ResPair.resConj 1).getD j #[]) v) ∧
          pairG
            (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA
              (nthD 0 XA x₁))
            (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA
              (nthD 0 XA x₂)) C₁ C₂ = (ResPair.n2 1).map (MulAut.conj U).toMonoidHom) := by
  obtain ⟨C₁, hC₁, hC₁i, hC₁m, hs₁⟩ := conj_spec (j := 2 * k) (by omega)
  obtain ⟨C₂, hC₂, hC₂i, hC₂m, hs₂⟩ := conj_spec (j := 2 * k + 1) (by omega)
  refine ⟨C₁, C₂, hC₁, hC₂, hC₁m, hC₂m, hs₁, hs₂, ?_⟩
  obtain ⟨hd₁, hr₁⟩ := dr_spec hx₁
  obtain ⟨hd₂, hr₂⟩ := dr_spec hx₂
  rw [grp_eq hx₁, grp_eq hx₂]
  have hrow := cp16966b_all (2 * k + nthD 0 DR x₁) (by
    change 2 * k + nthD 0 DR x₁ < 4
    omega)
  unfold row at hrow
  rw [div_two hd₁, mod_two hd₁] at hrow
  have hp := (allBelow_iff _ _).1 hrow _ hd₂
  unfold pair letQ at hp
  have hTH : ∀ v, linP CFSG.KD.GUC1.TH v = theta0 v := by
    rw [CFSG.KD.GUC1.cg_eq.2]
    exact linP_TH
  have hL : ∀ m, ∃ x ∈ compOf 1, ∀ v, linOfRows x v = linP (subQ L m) v := by
    unfold L
    rw [CFSG.KD.GUC1.cg_eq.1]
    exact (compOf_iff (by norm_num)).1
  have hL' : ∀ x ∈ compOf 1, ∃ m < 32, ∀ v, linOfRows x v = linP (subQ L m) v := by
    unfold L
    rw [CFSG.KD.GUC1.cg_eq.1]
    exact (compOf_iff (by norm_num)).2
  rcases pairW_spec hp (cand_mem hr₁) (cand_mem hr₂) (fun M hM => cand_le hr₁ hM)
      (fun M hM => cand_le hr₂ hM) rfl rfl hC₁ hC₁i hC₂ hC₂i hTH hL hL' n2_mem
      (fun M hM => n2_le' hM) with hv | ⟨j, hj, U, hU, heq⟩
  · exact Or.inl hv
  · have hj' : j < (ResPair.resConj 1).length := by
      rw [cp16966b_rc, List.length_map] at hj
      exact hj
    rw [cp16966b_rc] at hU
    exact Or.inr ⟨j, hj', U, rc_rows cp16966b_rcrows hj' hU, heq⟩

end CFSG.KD.GUP1

end
