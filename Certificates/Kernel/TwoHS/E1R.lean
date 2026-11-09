module

public import Certificates.Kernel.TwoHS.E1
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/e1r.txt" 431289 10426228798584572611

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

theorem e1pW1 : Nat.beq (wfC L (sigWords.getD 0 []) idK) E1W1 = true := by quickRfl
theorem e1pW2 : Nat.beq (wfC L (sigWords.getD 1 []) idK) E1W2 = true := by quickRfl
theorem e1pW3 : Nat.beq (wfC L (sigWords.getD 2 []) idK) E1W3 = true := by quickRfl
theorem e1pW4 : Nat.beq (wfC L (sigWords.getD 3 []) idK) E1W4 = true := by quickRfl
theorem e1pW5 : Nat.beq (wfC L (sigWords.getD 4 []) idK) E1W5 = true := by quickRfl
theorem e1pW6 : Nat.beq (wfC L (sigWords.getD 5 []) idK) E1W6 = true := by quickRfl
theorem e1pG2 : Nat.beq (wfC L gamma2Word idK) E1G2 = true := by quickRfl
theorem e1pG2I : Nat.beq (wfC L gamma2Word.reverse idK) E1G2I = true := by quickRfl

@[expose] noncomputable def SGWV (l : Nat) : Nat := [E1W1, E1W2, E1W3, E1W4, E1W5, E1W6].getD (l - 1) idK

theorem SGW_V : SGW = SGWV := by
  funext l
  unfold SGW SGWV
  generalize l - 1 = k
  match k with
  | 0 => exact e1WK (wd := sigWords.getD 0 []) (v := E1W1) e1pW1
  | 1 => exact e1WK (wd := sigWords.getD 1 []) (v := E1W2) e1pW2
  | 2 => exact e1WK (wd := sigWords.getD 2 []) (v := E1W3) e1pW3
  | 3 => exact e1WK (wd := sigWords.getD 3 []) (v := E1W4) e1pW4
  | 4 => exact e1WK (wd := sigWords.getD 4 []) (v := E1W5) e1pW5
  | 5 => exact e1WK (wd := sigWords.getD 5 []) (v := E1W6) e1pW6
  | k + 6 =>
    rw [List.getD_eq_default _ _ (by simp [sigWords]), List.getD_eq_default _ _ (by simp)]
    rfl

theorem e1pS0 : Nat.beq (wfC SGWV (betaWords.getD 0 []) idK) E1S0 = true := by quickRfl
theorem e1pS1 : Nat.beq (wfC SGWV (betaWords.getD 1 []) idK) E1S1 = true := by quickRfl
theorem e1pS2 : Nat.beq (wfC SGWV (betaWords.getD 2 []) idK) E1S2 = true := by quickRfl

theorem e1S_V {j s : Nat} (h : Nat.beq (wfC SGWV (betaWords.getD j []) idK) s = true) :
    SBK 1 j = s := by
  have e := Nat.eq_of_beq_eq_true h
  unfold SBK
  simp only [one_ne_zero, ↓reduceIte]
  rw [WK_sigWord, wfoldK_eq_C, SGW_V]
  exact e

@[expose] noncomputable def realKS (g gi s : Nat) (d : List Nat) (j : Nat) : Bool :=
  invEqK 11200 14 (mask 14) (11200 * 14) g gi &&
    Nat.beq (pc (pc g s) gi) (KPV (colOf d ([0, 1, 3].getD j 0)))

theorem realK_g2 {j s : Nat} (hs : SBK 1 j = s) :
    realK gamma2Word 1 gamma2Data j = realKS E1G2 E1G2I s gamma2Data j := by
  unfold realK realKS
  rw [hs, KP_V, e1WK (wd := gamma2Word) (v := E1G2) e1pG2]
  unfold WKI
  rw [e1WK (wd := gamma2Word.reverse) (v := E1G2I) e1pG2I]

theorem real_g2_0 : realK gamma2Word 1 gamma2Data 0 = true := by
  rewrite [realK_g2 (e1S_V (j := 0) (s := E1S0) e1pS0)]
  quickRfl
theorem real_g2_1 : realK gamma2Word 1 gamma2Data 1 = true := by
  rewrite [realK_g2 (e1S_V (j := 1) (s := E1S1) e1pS1)]
  quickRfl
theorem real_g2_2 : realK gamma2Word 1 gamma2Data 2 = true := by
  rewrite [realK_g2 (e1S_V (j := 2) (s := E1S2) e1pS2)]
  quickRfl

end CFSG.KD.TwoHS

end
