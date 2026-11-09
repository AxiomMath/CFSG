module

public import Certificates.Kernel.TwoHS.WKChainCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModCheck
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

#kwk_chain Sg0 24 (sigWords.getD 0 [])
#kwk_chain Sg1 24 (sigWords.getD 1 [])
#kwk_chain Sg2 24 (sigWords.getD 2 [])
#kwk_chain Sg3 24 (sigWords.getD 3 [])
#kwk_chain Sg4 24 (sigWords.getD 4 [])
#kwk_chain Sg5 24 (sigWords.getD 5 [])
#kwk_chain Bk0 24 (betaWords.getD 0 [])
#kwk_chain Bk1 24 (betaWords.getD 1 [])
#kwk_chain Bk2 24 (betaWords.getD 2 [])
#kwk_chain Tk 24 tWord

@[expose] noncomputable def SGWP_hy (l : Nat) : Nat :=
  [Sg0.v, Sg1.v, Sg2.v, Sg3.v, Sg4.v, Sg5.v].getD (l - 1) idK

theorem sigWords_getD_of_hy {k : Nat} (hk : 6 ≤ k) : sigWords.getD k [] = [] :=
  List.getD_eq_default _ _ (by rw [show sigWords.length = 6 from rfl]; exact hk)

theorem SGW_fun_hy : SGW_hy = SGWP_hy := by
  funext l
  show WK (sigWords.getD (l - 1) []) = [Sg0.v, Sg1.v, Sg2.v, Sg3.v, Sg4.v, Sg5.v].getD (l - 1) idK
  generalize l - 1 = k
  match k with
  | 0 => exact Sg0.eq
  | 1 => exact Sg1.eq
  | 2 => exact Sg2.eq
  | 3 => exact Sg3.eq
  | 4 => exact Sg4.eq
  | 5 => exact Sg5.eq
  | k + 6 =>
    rw [sigWords_getD_of_hy (by omega), List.getD_eq_default _ _ (by simp)]
    rfl

@[expose] noncomputable def BWP (j : Nat) : Nat := [Bk0.v, Bk1.v, Bk2.v].getD j idK

theorem betaWords_getD_of' {j : Nat} (hj : 3 ≤ j) : betaWords.getD j [] = [] :=
  List.getD_eq_default _ _ (by rw [show betaWords.length = 3 from rfl]; exact hj)

theorem WK_betaW (j : Nat) : WK (betaW j) = BWP j := by
  show WK (betaWords.getD j []) = [Bk0.v, Bk1.v, Bk2.v].getD j idK
  match j with
  | 0 => exact Bk0.eq
  | 1 => exact Bk1.eq
  | 2 => exact Bk2.eq
  | j + 3 =>
    rw [betaWords_getD_of' (by omega), List.getD_eq_default _ _ (by simp)]
    rfl

theorem betaW_letters (j : Nat) : lettersOK (betaW j) = true := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 =>
    show lettersOK (betaWords.getD (j + 3) []) = true
    rw [betaWords_getD_of' (by omega)]
    rfl

theorem tWord_letters : lettersOK tWord = true := rfl

theorem rptW_letters {w : List Nat} (h : lettersOK w = true) : ∀ k, lettersOK (rptW w k) = true
  | 0 => rfl
  | k + 1 => by
    have e : rptW w (k + 1) = w ++ rptW w k := by simp [rptW, List.replicate_succ]
    rw [e]
    unfold lettersOK at h ⊢
    rw [List.all_append, h]
    exact rptW_letters h k

theorem WK_rptW {w : List Nat} (h : lettersOK w = true) : ∀ k, WK (rptW w k) = pw (WK w) k
  | 0 => rfl
  | k + 1 => by
    have e : rptW w (k + 1) = w ++ rptW w k := by simp [rptW, List.replicate_succ]
    rw [e, WK_append_hy h (rptW_letters h k), WK_rptW h k]
    change _ = strictN (CFSG.KC.PkPow.ppw 11200 14 (WK w) k) (fun q => pcomp 11200 14 (mask 14) (WK w) q)
    rw [CFSG.KS.PEnum.strictN_app']
    rfl

theorem WK_rptW_beta (j k : Nat) : WK (rptW (betaW j) k) = pw (BWP j) k := by
  rw [WK_rptW (betaW_letters j), WK_betaW]

theorem WK_rptW_t (k : Nat) : WK (rptW tWord k) = pw Tk.v k := by
  rw [WK_rptW tWord_letters, Tk.eq]

theorem lettersOK_append (u v : List Nat) : lettersOK (u ++ v) = (lettersOK u && lettersOK v) := by
  unfold lettersOK
  exact List.all_append

theorem WK_kapW (c : List Nat) : WK (kapW c) =
    pc (pc (pc (pw (BWP 0) (c.getD 0 0)) (pw (BWP 1) (c.getD 1 0))) (pw Tk.v (c.getD 2 0 / 2)))
      (pw (BWP 2) (c.getD 3 0)) := by
  have h0 := rptW_letters (betaW_letters 0) (c.getD 0 0)
  have h1 := rptW_letters (betaW_letters 1) (c.getD 1 0)
  have ht := rptW_letters tWord_letters (c.getD 2 0 / 2)
  have h2 := rptW_letters (betaW_letters 2) (c.getD 3 0)
  have h01 : lettersOK (rptW (betaW 0) (c.getD 0 0) ++ rptW (betaW 1) (c.getD 1 0)) = true := by
    rw [lettersOK_append, h0, h1]
    rfl
  have h01t : lettersOK (rptW (betaW 0) (c.getD 0 0) ++ rptW (betaW 1) (c.getD 1 0) ++
      rptW tWord (c.getD 2 0 / 2)) = true := by
    rw [lettersOK_append, h01, ht]
    rfl
  unfold kapW
  rw [WK_append_hy h01t h2, WK_append_hy h01 ht, WK_append_hy h0 h1, WK_rptW_beta, WK_rptW_beta,
    WK_rptW_beta, WK_rptW_t]

theorem comm_of_central {g x : Nat} (hg : Cn g) (hx : (Nat.beq x idK || Nat.beq x Tk.v) = true)
    (ht : Nat.beq (pc g Tk.v) (pc Tk.v g) = true) : Nat.beq (pc g x) (pc x g) = true := by
  rcases Bool.or_eq_true_iff.1 hx with h | h
  · rw [Nat.eq_of_beq_eq_true h, pc_idK_right_hy hg, pc_idK_left_hy hg]
    exact Nat.beq_refl g
  · rw [Nat.eq_of_beq_eq_true h]
    exact ht

end CFSG.KD.TwoHS

end
