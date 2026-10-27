
module

public import Certificates.Kernel.GammaU.ResPairOK
public import Certificates.Kernel.GammaU.Triple
public import Certificates.Kernel.GammaU.PairBridge
public import CFSG.Certificates.Kernel.GammaUPairSound

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GURPB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUV CFSG.KC.GUS CFSG.KD.GUTB
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.ResPair

theorem resPair_of {i : Nat} {N2 : List Nat} {NN : Nat} {c : Array ℕ} {Ci : Nat} {L : List Nat}
    {TH tg : Nat} {rec : List (List Nat)} (hN : ∀ e < NN, ∃ U ∈ ResPair.n2 i, IsP U (nthD 0 N2 e))
    (hrow : rowsOK c.toList = true) (hinv : mulP (packR c) Ci = idP)
    (hTH : ∀ v, linP TH v = theta0 v)
    (hL : ∀ m, ∃ x ∈ compOf i, ∀ v, linOfRows x v = linP (subQ L m) v)
    (hL' : ∀ x ∈ compOf i, ∃ m < 32, ∀ v, linOfRows x v = linP (subQ L m) v)
    (h : (bif Nat.beq tg 0 then d2aOK L TH (letT N2 NN (nthD 0 N2) (packR c) Ci) (Nat.add NN NN) rec
      else Nat.beq tg 1 && d1OK L (letT N2 NN (nthD 0 N2) (packR c) Ci) (Nat.add NN NN) rec) =
        true) :
    ∃ (h1 : mulR c (invR c) = idR) (h2 : mulR (invR c) c = idR),
      Violation (genGrp (n2Gens i) ⊔
        (genGrp (n2Gens i)).map (MulAut.conj (eqvOf c (invR c) h1 h2)).toMonoidHom)
        (compOf i) (idR :: hyp10 i) := by
  obtain ⟨U, hU⟩ := IsP.exists_of_mul hinv
  have hUc : ∀ v, U v = linOfRows c v := (isP_packR hrow U).1 hU
  obtain ⟨h1, h2⟩ := CFSG.KD.GUBB.inv_ok hrow ⟨U, hUc⟩
  refine ⟨h1, h2, ?_⟩
  have hVe : eqvOf c (invR c) h1 h2 = U := LinearEquiv.ext fun v => (hUc v).symm
  rw [hVe]
  have hUi : IsP U⁻¹ Ci := hU.inv hinv
  have hf : ∀ e < Nat.add NN NN, ∃ V ∈ genGrp (n2Gens i) ⊔
      (genGrp (n2Gens i)).map (MulAut.conj U).toMonoidHom,
      IsP V (letT N2 NN (nthD 0 N2) (packR c) Ci e) := by
    intro e he
    unfold letT
    by_cases hlt : e < NN
    · rw [blt_true hlt, cond_true]
      obtain ⟨V, hV, hVP⟩ := hN e hlt
      exact ⟨V, Subgroup.mem_sup_left hV, hVP⟩
    · rw [blt_false hlt, cond_false]
      obtain ⟨V, hV, hVP⟩ := hN (e - NN) (by change e < NN + NN at he; omega)
      exact ⟨_, Subgroup.mem_sup_right ⟨V, hV, rfl⟩, isP_conj hU hUi hVP⟩
  cases ht : Nat.beq tg 0
  · rw [ht, cond_false, Bool.and_eq_true] at h
    exact d1OK_spec h.2 hf hL hL'
  · rw [ht, cond_true] at h
    exact d2aOK_spec h hf hTH hL

theorem resConj_zero (i : Nat) (h : 0 < (ResPair.resConj i).length) :
    (ResPair.resConj i)[0] = idR := by
  have h0 : (ResPair.resConj i)[0]'h = (ResPair.resConj i).headD #[] := by
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem h,
      Option.getD_some]
  rw [h0]
  unfold ResPair.resConj
  split <;> decide

theorem resPair0 {c : Array ℕ} (hc : c ∈ ResPair.resConj 0) (hc1 : c ≠ idR) :
    ∃ (h1 : mulR c (invR c) = idR) (h2 : mulR (invR c) c = idR),
      Violation (genGrp (n2Gens 0) ⊔
        (genGrp (n2Gens 0)).map (MulAut.conj (eqvOf c (invR c) h1 h2)).toMonoidHom)
        (compOf 0) (idR :: hyp10 0) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  cases j with
  | zero => exact (hc1 (resConj_zero 0 hj)).elim
  | succ j =>
    obtain ⟨-, -, -, -, hNN, -, -⟩ := CFSG.KD.GUT0.lists_spec
    have hN : ∀ e < CFSG.KD.GUT0.NN, ∃ U ∈ ResPair.n2 0, IsP U (nthD 0 CFSG.KD.GUT0.N2 e) := by
      intro e he
      rw [CFSG.KD.GUT0.ct16966a_n2]
      refine n2_isP CFSG.KD.GUS0.cs16981a_rows CFSG.KD.GUS0.cs16981a_inv e ?_
      rw [hNN, CFSG.KD.GUT0.ct16966a_n2, List.length_map] at he
      exact he
    have hrc : nthD 0 CFSG.KD.GUP0.RC (j + 1) = packR (ResPair.resConj 0)[j + 1] := by
      rw [CFSG.KD.GUP0.cp16966a_rc, nthD_map _ _ _ #[] hj, getD_of_lt _ hj]
    have hl : (ResPair.resConj 0).length = 30 := rfl
    have hinv := CFSG.KD.GUN0.lists_spec.2.2.2.2 (j + 1) (by omega)
    rw [hrc] at hinv
    have hj29 : j < 29 := by omega
    have h := CFSG.KD.GURP0.cr16980a_all j hj29
    have e : Nat.add j 1 = j + 1 := rfl
    unfold CFSG.KD.GURP0.rp CFSG.KD.GURP0.letR at h
    rw [e, hrc] at h
    exact resPair_of (L := CFSG.KD.GUT0.L) hN
      (List.all_eq_true.1 CFSG.KD.GUP0.cp16966a_rcrows _ (List.getElem_mem hj)) hinv linP_TH
      (compOf_iff (by norm_num)).1 (compOf_iff (by norm_num)).2 h

theorem resPair1 {c : Array ℕ} (hc : c ∈ ResPair.resConj 1) (hc1 : c ≠ idR) :
    ∃ (h1 : mulR c (invR c) = idR) (h2 : mulR (invR c) c = idR),
      Violation (genGrp (n2Gens 1) ⊔
        (genGrp (n2Gens 1)).map (MulAut.conj (eqvOf c (invR c) h1 h2)).toMonoidHom)
        (compOf 1) (idR :: hyp10 1) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  cases j with
  | zero => exact (hc1 (resConj_zero 1 hj)).elim
  | succ j =>
    obtain ⟨-, -, -, -, hNN, -, -⟩ := CFSG.KD.GUT1.lists_spec
    have hN : ∀ e < CFSG.KD.GUT1.NN, ∃ U ∈ ResPair.n2 1, IsP U (nthD 0 CFSG.KD.GUT1.N2 e) := by
      intro e he
      rw [CFSG.KD.GUT1.ct16966b_n2]
      refine n2_isP CFSG.KD.GUS1.cs16981b_rows CFSG.KD.GUS1.cs16981b_inv e ?_
      rw [hNN, CFSG.KD.GUT1.ct16966b_n2, List.length_map] at he
      exact he
    have hTH : ∀ v, linP CFSG.KD.GUC1.TH v = theta0 v := by
      rw [CFSG.KD.GUC1.cg_eq.2]
      exact linP_TH
    have hL : ∀ m, ∃ x ∈ compOf 1, ∀ v, linOfRows x v = linP (subQ CFSG.KD.GUT1.L m) v := by
      unfold CFSG.KD.GUT1.L
      rw [CFSG.KD.GUC1.cg_eq.1]
      exact (compOf_iff (by norm_num)).1
    have hL' : ∀ x ∈ compOf 1, ∃ m < 32, ∀ v, linOfRows x v = linP (subQ CFSG.KD.GUT1.L m) v := by
      unfold CFSG.KD.GUT1.L
      rw [CFSG.KD.GUC1.cg_eq.1]
      exact (compOf_iff (by norm_num)).2
    have hrc : nthD 0 CFSG.KD.GUP1.RC (j + 1) = packR (ResPair.resConj 1)[j + 1] := by
      rw [CFSG.KD.GUP1.cp16966b_rc, nthD_map _ _ _ #[] hj, getD_of_lt _ hj]
    have hl : (ResPair.resConj 1).length = 30 := rfl
    have hinv := CFSG.KD.GUN1.lists_spec.2.2.2.2 (j + 1) (by omega)
    rw [hrc] at hinv
    have hj29 : j < 29 := by omega
    have h := CFSG.KD.GURP1.cr16980b_all j hj29
    have e : Nat.add j 1 = j + 1 := rfl
    unfold CFSG.KD.GURP1.rp CFSG.KD.GURP1.letR at h
    rw [e, hrc] at h
    exact resPair_of hN
      (List.all_eq_true.1 CFSG.KD.GUP1.cp16966b_rcrows _ (List.getElem_mem hj)) hinv hTH hL hL' h

theorem resPairFacts : ∀ i, i = 0 ∨ i = 1 → ∀ c ∈ ResPair.resConj i, c ≠ idR →
    ∃ (h1 : mulR c (invR c) = idR) (h2 : mulR (invR c) c = idR),
      Violation (genGrp (n2Gens i) ⊔
        (genGrp (n2Gens i)).map (MulAut.conj (eqvOf c (invR c) h1 h2)).toMonoidHom)
        (compOf i) (idR :: hyp10 i) := by
  rintro i (rfl | rfl)
  · exact fun c hc hc1 => resPair0 hc hc1
  · exact fun c hc hc1 => resPair1 hc hc1

end CFSG.KD.GURPB

end
