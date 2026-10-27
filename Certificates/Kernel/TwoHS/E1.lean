module

public import Certificates.Kernel.TwoHS.HYOps
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.TwoHS

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

theorem e1_inv : ((List.range 3).all fun j => invEqK 11200 14 (mask 14) (11200 * 14) (BK j) (BKI j)) &&
    invEqK 11200 14 (mask 14) (11200 * 14) TK TKI = true := by quickRfl

theorem e1_t : (Nat.beq (pc TK TK) idK && !Nat.beq TK idK) = true := by quickRfl

theorem e1_tc : allN 6 (fun j => Nat.beq (pc TK (HY.F j)) (pc (HY.F j) TK)) = true := by quickRfl

theorem e1_bc : ((List.range 3).all fun i => (List.range 3).all fun j =>
    Nat.beq (pc (BK i) (BK j)) (pc (BK j) (BK i))) = true := by quickRfl

theorem e1_b4 : ((List.range 3).all fun j => Nat.beq (pw (BK j) 4) idK) = true := by quickRfl

theorem e1_a0 : ((List.range 4).all fun b => (List.range 4).all fun c => (List.range 2).all fun u =>
    ((0 : Nat) == 0 && b == 0 && c == 0 && u == 0) || !Nat.beq (E1K 0 b c u) idK) = true := by
  quickRfl
theorem e1_a1 : ((List.range 4).all fun b => (List.range 4).all fun c => (List.range 2).all fun u =>
    ((1 : Nat) == 0 && b == 0 && c == 0 && u == 0) || !Nat.beq (E1K 1 b c u) idK) = true := by
  quickRfl
theorem e1_a2 : ((List.range 4).all fun b => (List.range 4).all fun c => (List.range 2).all fun u =>
    ((2 : Nat) == 0 && b == 0 && c == 0 && u == 0) || !Nat.beq (E1K 2 b c u) idK) = true := by
  quickRfl
theorem e1_a3 : ((List.range 4).all fun b => (List.range 4).all fun c => (List.range 2).all fun u =>
    ((3 : Nat) == 0 && b == 0 && c == 0 && u == 0) || !Nat.beq (E1K 3 b c u) idK) = true := by
  quickRfl

@[expose] noncomputable def realK (lw : List Nat) (b : Nat) (d : List Nat) (j : Nat) : Bool :=
  invEqK 11200 14 (mask 14) (11200 * 14) (WK lw) (WKI lw) &&
    Nat.beq (pc (pc (WK lw) (SBK b j)) (WKI lw)) (KP (colOf d ([0, 1, 3].getD j 0)))

theorem real_g1_0 : realK gamma1Word 0 gamma1Data 0 = true := by quickRfl
theorem real_g1_1 : realK gamma1Word 0 gamma1Data 1 = true := by quickRfl
theorem real_g1_2 : realK gamma1Word 0 gamma1Data 2 = true := by quickRfl

end CFSG.KD.TwoHS

end
