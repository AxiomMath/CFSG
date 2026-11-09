module

public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Kernel.TwoHS.WKVal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/e1p.txt" 392080 671958300029178516

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def BK (j : Nat) : Nat := WK (betaWords.getD j [])

@[expose] noncomputable def BKI (j : Nat) : Nat := WKI (betaWords.getD j [])

@[expose] noncomputable def TK : Nat := WK tWord

@[expose] noncomputable def TKI : Nat := WKI tWord

@[expose] noncomputable def E1K (a b c u : Nat) : Nat :=
  pc (pc (pc (pw (BK 0) a) (pw (BK 1) b)) (pw (BK 2) c)) (pw TK u)

@[expose] noncomputable def KP (c : List Nat) : Nat :=
  pc (pc (pc (pw (BK 0) (c.getD 0 0)) (pw (BK 1) (c.getD 1 0))) (pw TK (c.getD 2 0 / 2)))
    (pw (BK 2) (c.getD 3 0))

@[expose] noncomputable def SBK (b j : Nat) : Nat :=
  if b = 0 then BK j else WK (sigWord (betaWords.getD j []))

theorem e1pB0 : Nat.beq (wfC L (betaWords.getD 0 []) idK) E1B0 = true := by quickRfl
theorem e1pB1 : Nat.beq (wfC L (betaWords.getD 1 []) idK) E1B1 = true := by quickRfl
theorem e1pB2 : Nat.beq (wfC L (betaWords.getD 2 []) idK) E1B2 = true := by quickRfl
theorem e1pBI0 : Nat.beq (wfC L (betaWords.getD 0 []).reverse idK) E1BI0 = true := by quickRfl
theorem e1pBI1 : Nat.beq (wfC L (betaWords.getD 1 []).reverse idK) E1BI1 = true := by quickRfl
theorem e1pBI2 : Nat.beq (wfC L (betaWords.getD 2 []).reverse idK) E1BI2 = true := by quickRfl
theorem e1pT : Nat.beq (wfC L tWord idK) E1T = true := by quickRfl
theorem e1pTI : Nat.beq (wfC L tWord.reverse idK) E1TI = true := by quickRfl
theorem e1pG : Nat.beq (wfC L gamma1Word idK) E1G = true := by quickRfl
theorem e1pGI : Nat.beq (wfC L gamma1Word.reverse idK) E1GI = true := by quickRfl

theorem e1WK {wd : List Nat} {v : Nat} (h : Nat.beq (wfC L wd idK) v = true) : WK wd = v := by
  have e := Nat.eq_of_beq_eq_true h
  rw [← wfoldK_eq_C] at e
  exact e

@[expose] noncomputable def BKV (j : Nat) : Nat := [E1B0, E1B1, E1B2].getD j idK

@[expose] noncomputable def BKIV (j : Nat) : Nat := [E1BI0, E1BI1, E1BI2].getD j idK

theorem BK_V : BK = BKV := by
  funext j
  match j with
  | 0 => exact e1WK (wd := betaWords.getD 0 []) (v := E1B0) e1pB0
  | 1 => exact e1WK (wd := betaWords.getD 1 []) (v := E1B1) e1pB1
  | 2 => exact e1WK (wd := betaWords.getD 2 []) (v := E1B2) e1pB2
  | j + 3 =>
    unfold BK BKV
    rw [List.getD_eq_default _ _ (by simp [betaWords]), List.getD_eq_default _ _ (by simp)]
    rfl

theorem BKI_V : BKI = BKIV := by
  funext j
  match j with
  | 0 => exact e1WK (wd := (betaWords.getD 0 []).reverse) (v := E1BI0) e1pBI0
  | 1 => exact e1WK (wd := (betaWords.getD 1 []).reverse) (v := E1BI1) e1pBI1
  | 2 => exact e1WK (wd := (betaWords.getD 2 []).reverse) (v := E1BI2) e1pBI2
  | j + 3 =>
    unfold BKI BKIV WKI
    rw [List.getD_eq_default _ _ (by simp [betaWords]), List.getD_eq_default _ _ (by simp)]
    rfl

theorem TK_V : TK = E1T := e1WK (wd := tWord) (v := E1T) e1pT

theorem TKI_V : TKI = E1TI := e1WK (wd := tWord.reverse) (v := E1TI) e1pTI

@[expose] noncomputable def KPV (c : List Nat) : Nat :=
  pc (pc (pc (pw (BKV 0) (c.getD 0 0)) (pw (BKV 1) (c.getD 1 0))) (pw E1T (c.getD 2 0 / 2)))
    (pw (BKV 2) (c.getD 3 0))

@[expose] noncomputable def SBKV (b j : Nat) : Nat :=
  if b = 0 then BKV j else WK (sigWord (betaWords.getD j []))

theorem KP_V : KP = KPV := by
  funext c
  unfold KP KPV
  rw [BK_V, TK_V]

theorem SBK_V : SBK = SBKV := by
  funext b j
  unfold SBK SBKV
  rw [BK_V]

theorem e1_inv : ((List.range 3).all fun j => invEqK 11200 14 (mask 14) (11200 * 14) (BK j) (BKI j)) &&
    invEqK 11200 14 (mask 14) (11200 * 14) TK TKI = true := by
  rewrite [BK_V, BKI_V, TK_V, TKI_V]
  quickRfl

theorem e1_t : (Nat.beq (pc TK TK) idK && !Nat.beq TK idK) = true := by
  rewrite [TK_V]
  quickRfl

theorem e1_tc : allN 6 (fun j => Nat.beq (pc TK (HY.F j)) (pc (HY.F j) TK)) = true := by
  rewrite [TK_V]
  quickRfl

theorem e1_bc : ((List.range 3).all fun i => (List.range 3).all fun j =>
    Nat.beq (pc (BK i) (BK j)) (pc (BK j) (BK i))) = true := by
  rewrite [BK_V]
  quickRfl

theorem e1_b4 : ((List.range 3).all fun j => Nat.beq (pw (BK j) 4) idK) = true := by
  rewrite [BK_V]
  quickRfl

@[expose] noncomputable def e1It (p e i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ r => pg 14 (mask 14) p r) e

@[expose] noncomputable def e1PtK (a b c u : Nat) : Nat :=
  e1It (BK 0) a (e1It (BK 1) b (e1It (BK 2) c (e1It TK u 1)))

@[expose] noncomputable def e1PtV (a b c u : Nat) : Nat :=
  e1It (BKV 0) a (e1It (BKV 1) b (e1It (BKV 2) c (e1It E1T u 1)))

theorem e1Pt_V : e1PtK = e1PtV := by
  funext a b c u
  unfold e1PtK e1PtV
  rw [BK_V, TK_V]

theorem e1_pt : ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
    (List.range 2).all fun u => (a == 0 && b == 0 && c == 0 && u == 0) || !Nat.beq (e1PtK a b c u) 1) =
    true := by
  rewrite [e1Pt_V]
  quickRfl

@[expose] noncomputable def realK (lw : List Nat) (b : Nat) (d : List Nat) (j : Nat) : Bool :=
  invEqK 11200 14 (mask 14) (11200 * 14) (WK lw) (WKI lw) &&
    Nat.beq (pc (pc (WK lw) (SBK b j)) (WKI lw)) (KP (colOf d ([0, 1, 3].getD j 0)))

@[expose] noncomputable def realKV (g gi : Nat) (b : Nat) (d : List Nat) (j : Nat) : Bool :=
  invEqK 11200 14 (mask 14) (11200 * 14) g gi &&
    Nat.beq (pc (pc g (SBKV b j)) gi) (KPV (colOf d ([0, 1, 3].getD j 0)))

theorem realK_g1 (j : Nat) : realK gamma1Word 0 gamma1Data j = realKV E1G E1GI 0 gamma1Data j := by
  unfold realK realKV
  rw [SBK_V, KP_V, e1WK e1pG]
  unfold WKI
  rw [e1WK e1pGI]

theorem real_g1_0 : realK gamma1Word 0 gamma1Data 0 = true := by
  rewrite [realK_g1]
  quickRfl
theorem real_g1_1 : realK gamma1Word 0 gamma1Data 1 = true := by
  rewrite [realK_g1]
  quickRfl
theorem real_g1_2 : realK gamma1Word 0 gamma1Data 2 = true := by
  rewrite [realK_g1]
  quickRfl

end CFSG.KD.TwoHS

end
