module

public import Certificates.Kernel.TwoHS.WKVal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyCheck
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/fyp.txt" 548914 6952424917582767875

public section

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.KS CFSG.KS.MulH

theorem pR : Nat.beq (wfC L fyRWord idK) FPR = true := by quickRfl
theorem pC0 : Nat.beq (wfC L (fyC 0) idK) FPC0 = true := by quickRfl
theorem pC1 : Nat.beq (wfC L (fyC 1) idK) FPC1 = true := by quickRfl
theorem pC2 : Nat.beq (wfC L (fyC 2) idK) FPC2 = true := by quickRfl
theorem pC3 : Nat.beq (wfC L (fyC 3) idK) FPC3 = true := by quickRfl
theorem pA : Nat.beq (wfC L fyAWord idK) FPA = true := by quickRfl
theorem pL : Nat.beq (wfC L fyLWord idK) FPL = true := by quickRfl
theorem pT : Nat.beq (wfC L tWord idK) FPT = true := by quickRfl
theorem sg0 : Nat.beq (wfC L (sigWords.getD 0 []) idK) SGWP0 = true := by quickRfl
theorem sg1 : Nat.beq (wfC L (sigWords.getD 1 []) idK) SGWP1 = true := by quickRfl
theorem sg2 : Nat.beq (wfC L (sigWords.getD 2 []) idK) SGWP2 = true := by quickRfl
theorem sg3 : Nat.beq (wfC L (sigWords.getD 3 []) idK) SGWP3 = true := by quickRfl
theorem sg4 : Nat.beq (wfC L (sigWords.getD 4 []) idK) SGWP4 = true := by quickRfl
theorem sg5 : Nat.beq (wfC L (sigWords.getD 5 []) idK) SGWP5 = true := by quickRfl

theorem WK_pin {wd : List Nat} {v : Nat} (h : Nat.beq (wfC L wd idK) v = true) : WK wd = v := by
  have e := Nat.eq_of_beq_eq_true h
  rw [← wfoldK_eq_C] at e
  exact e

theorem WK_fyR : WK fyRWord = FPR := WK_pin pR
theorem WK_fyC0 : WK (fyC 0) = FPC0 := WK_pin pC0
theorem WK_fyC1 : WK (fyC 1) = FPC1 := WK_pin pC1
theorem WK_fyC2 : WK (fyC 2) = FPC2 := WK_pin pC2
theorem WK_fyC3 : WK (fyC 3) = FPC3 := WK_pin pC3
theorem WK_fyA : WK fyAWord = FPA := WK_pin pA
theorem WK_fyL : WK fyLWord = FPL := WK_pin pL
theorem WK_fyT : WK tWord = FPT := WK_pin pT

@[expose] noncomputable def SGWP : Nat → Nat
  | 0 => SGWP0
  | 1 => SGWP0
  | 2 => SGWP1
  | 3 => SGWP2
  | 4 => SGWP3
  | 5 => SGWP4
  | 6 => SGWP5
  | _ => idK

theorem sigWords_getD_of {k : Nat} (hk : 6 ≤ k) : sigWords.getD k [] = [] := by
  have h : sigWords.length = 6 := rfl
  exact List.getD_eq_default _ _ (by omega)

theorem SGW_fun : SGW = SGWP := by
  funext l
  match l with
  | 0 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg0
  | 1 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg0
  | 2 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg1
  | 3 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg2
  | 4 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg3
  | 5 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg4
  | 6 =>
    simp only [SGW, SGWP, Nat.reduceSub]
    exact WK_pin sg5
  | k + 7 =>
    have e : k + 7 - 1 = k + 6 := by omega
    unfold SGW
    rw [e, sigWords_getD_of (by omega)]
    rfl

theorem lettersOK_cat (u v : List Nat) : lettersOK (u ++ v) = (lettersOK u && lettersOK v) := by
  unfold lettersOK
  exact List.all_append

theorem lOK_R : lettersOK fyRWord = true := by decide
theorem lOK_C0 : lettersOK (fyC 0) = true := by decide
theorem lOK_C1 : lettersOK (fyC 1) = true := by decide
theorem lOK_C2 : lettersOK (fyC 2) = true := by decide
theorem lOK_C3 : lettersOK (fyC 3) = true := by decide
theorem lOK_A : lettersOK fyAWord = true := by decide
theorem lOK_L : lettersOK fyLWord = true := by decide
theorem lOK_T : lettersOK tWord = true := by decide
theorem lOK_nil : lettersOK [] = true := rfl

theorem WK_sigWordP (w : List Nat) : WK (sigWord w) = wfC SGWP w idK := by
  rw [WK_sigWord, SGW_fun, wfoldK_eq_C]

end CFSG.KD.TwoHS

end
