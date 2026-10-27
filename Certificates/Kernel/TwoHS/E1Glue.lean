module

public import Certificates.Kernel.TwoHS.E1R
public import Certificates.Kernel.TwoHS.HYOpsGlue

public section

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.KS.MulH CFSG.KS.Prim
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

theorem betaWords_letters : betaWords.all lettersOK = true := by decide

theorem beta_parts {j : Nat} (hj : j < 3) :
    betaT j = tabT (CFSG.KS.Raw.unpack 11200 14 (BK j)) ∧ Cn (BK j) ∧
      invT 11200 (betaT j) = tabT (CFSG.KS.Raw.unpack 11200 14 (BKI j)) ∧ Cn (BKI j) ∧
      permOK 11200 (betaT j) = true ∧ invOK 11200 (betaT j) (invT 11200 (betaT j)) = true :=
  word_inv (lettersOK_getD betaWords_letters j)
    (List.all_eq_true.1 (Bool.and_eq_true_iff.1 e1_inv).1 j (List.mem_range.2 hj))

theorem t_parts :
    tT = tabT (CFSG.KS.Raw.unpack 11200 14 TK) ∧ Cn TK ∧
      invT 11200 tT = tabT (CFSG.KS.Raw.unpack 11200 14 TKI) ∧ Cn TKI ∧
      permOK 11200 tT = true ∧ invOK 11200 tT (invT 11200 tT) = true :=
  word_inv (by decide) (Bool.and_eq_true_iff.1 e1_inv).2

theorem pow_beta {j : Nat} (hj : j < 3) (e : Nat) :
    powT 11200 e (betaT j) = tabT (CFSG.KS.Raw.unpack 11200 14 (pw (BK j) e)) ∧
      Cn (pw (BK j) e) := by
  rw [(beta_parts hj).1]
  exact powT_eq (beta_parts hj).2.1 e

theorem pow_t (e : Nat) :
    powT 11200 e tT = tabT (CFSG.KS.Raw.unpack 11200 14 (pw TK e)) ∧ Cn (pw TK e) := by
  rw [t_parts.1]
  exact powT_eq t_parts.2.1 e

theorem e1T_eq (a b c u : Nat) :
    e1T a b c u = tabT (CFSG.KS.Raw.unpack 11200 14 (E1K a b c u)) ∧ Cn (E1K a b c u) := by
  have h0 := pow_beta (j := 0) (by norm_num) a
  have h1 := pow_beta (j := 1) (by norm_num) b
  have h2 := pow_beta (j := 2) (by norm_num) c
  have h3 := pow_t u
  unfold e1T E1K
  rw [h0.1, h1.1, h2.1, h3.1, comp_eq h0.2 h1.2, comp_eq (cPc h0.2 h1.2) h2.2,
    comp_eq (cPc (cPc h0.2 h1.2) h2.2) h3.2]
  exact ⟨rfl, cPc (cPc (cPc h0.2 h1.2) h2.2) h3.2⟩

theorem kapT_eq (c : List Nat) :
    kapT c = tabT (CFSG.KS.Raw.unpack 11200 14 (KP c)) ∧ Cn (KP c) := by
  have h0 := pow_beta (j := 0) (by norm_num) (c.getD 0 0)
  have h1 := pow_beta (j := 1) (by norm_num) (c.getD 1 0)
  have h3 := pow_t (c.getD 2 0 / 2)
  have h2 := pow_beta (j := 2) (by norm_num) (c.getD 3 0)
  unfold kapT KP
  rw [h0.1, h1.1, h3.1, h2.1, comp_eq h0.2 h1.2, comp_eq (cPc h0.2 h1.2) h3.2,
    comp_eq (cPc (cPc h0.2 h1.2) h3.2) h2.2]
  exact ⟨rfl, cPc (cPc (cPc h0.2 h1.2) h3.2) h2.2⟩

theorem sigBeta_eq {b j : Nat} (hb : b < 2) (hj : j < 3) :
    sigBetaT b j = tabT (CFSG.KS.Raw.unpack 11200 14 (SBK b j)) ∧ Cn (SBK b j) := by
  unfold sigBetaT SBK
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp only [if_true]
    exact ⟨(beta_parts hj).1, (beta_parts hj).2.1⟩
  · simp only [one_ne_zero, if_false]
    exact wordTbl_eq (lettersOK_sigWord (betaWords.getD j []))

theorem realEq_of {lw : List Nat} {b : Nat} {d : List Nat} {j : Nat} (hb : b < 2) (hj : j < 3)
    (hl : lettersOK lw = true) (h : realK lw b d j = true) : realEq lw b d j = true := by
  unfold realK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨e, c, ei, ci, -, hinv⟩ := word_inv hl h.1
  obtain ⟨es, cs⟩ := sigBeta_eq hb hj
  obtain ⟨ek, ck⟩ := kapT_eq (colOf d ([0, 1, 3].getD j 0))
  simp only [realEq]
  rw [hinv, Bool.true_and, conjT, ei, e, es, ek, comp_eq c cs, comp_eq (cPc c cs) ci,
    tblEq_eq (cPc (cPc c cs) ci) ck]
  exact h.2

theorem e1OK_true : e1OK = true := by
  have cA : (List.range 3).all (fun j =>
      permOK 11200 (betaT j) && invOK 11200 (betaT j) (invT 11200 (betaT j))) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [(beta_parts hj').2.2.2.2.1, (beta_parts hj').2.2.2.2.2]
    rfl
  have cD : involOK 11200 tT = true := by
    rw [t_parts.1, involOK_eq t_parts.2.1]
    have h := e1_t
    rw [Bool.and_eq_true] at h
    rw [h.1]
    cases e : Nat.beq TK idK
    · rfl
    · rw [e] at h
      exact absurd h.2 (by decide)
  have cE : harYs.all (commTT 11200 tT) = true := by
    refine harYs_all fun i => ?_
    rw [t_parts.1, commTT_eq t_parts.2.1 (hy i.isLt).1]
    exact CFSG.KS.allN_spec e1_tc i.val i.isLt
  have cF : (List.range 3).all (fun i => (List.range 3).all fun j =>
      commTT 11200 (betaT i) (betaT j)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    rw [(beta_parts hi').1, (beta_parts hj').1,
      commTT_eq (beta_parts hi').2.1 (beta_parts hj').2.1]
    exact List.all_eq_true.1 (List.all_eq_true.1 e1_bc i hi) j hj
  have cG : (List.range 3).all (fun j => tblEq 11200 (powT 11200 4 (betaT j)) (idT 11200)) =
      true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [(pow_beta hj' 4).1, idT_eq, tblEq_eq (pow_beta hj' 4).2 cId]
    exact List.all_eq_true.1 e1_b4 j hj
  have hE : ∀ a b c u, tblEq 11200 (e1T a b c u) (idT 11200) = Nat.beq (E1K a b c u) idK := by
    intro a b c u
    rw [(e1T_eq a b c u).1, idT_eq, tblEq_eq (e1T_eq a b c u).2 cId]
  have cH : (List.range 4).all (fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 2).all fun u =>
        (a == 0 && b == 0 && c == 0 && u == 0) || !tblEq 11200 (e1T a b c u) (idT 11200)) =
      true := by
    simp only [hE]
    rw [List.all_eq_true]
    intro a ha
    have ha' := List.mem_range.1 ha
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl
    · exact e1_a0
    · exact e1_a1
    · exact e1_a2
    · exact e1_a3
  unfold e1OK
  simp only [cA, t_parts.2.2.2.2.1, t_parts.2.2.2.2.2, cD, cE, cF, cG, cH, Bool.and_self]

theorem realOK_true : realOK = true := by
  have cA : (List.range 3).all (fun j =>
      realEq gamma1Word 0 gamma1Data j && realEq gamma2Word 1 gamma2Data j) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have h1 : realK gamma1Word 0 gamma1Data j = true := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact real_g1_0
      · exact real_g1_1
      · exact real_g1_2
    have h2 : realK gamma2Word 1 gamma2Data j = true := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact real_g2_0
      · exact real_g2_1
      · exact real_g2_2
    rw [realEq_of (lw := gamma1Word) (b := 0) (by norm_num) hj' (by decide) h1,
      realEq_of (lw := gamma2Word) (b := 1) (by norm_num) hj' (by decide) h2]
    rfl
  have cB : (realShapeOK 0 gamma1Data && realShapeOK 1 gamma2Data) = true := by decide
  unfold realOK
  rw [Bool.and_assoc, cA, cB]
  rfl

end CFSG.KD.TwoHS

end
