module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Data.Kernel.O8.SARoots
public import Certificates.Data.E4QuatO8Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] def r127W : List (List Int × Nat) :=
  [(CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [1], 2),
    (CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [2, 2], 4)]

@[expose] def r127Ty (k : Nat) : Nat := repTypes.getD k 0

@[expose] def r127Fix : List Nat := [72, 32, 24, 64, 16]

@[expose] noncomputable def r127M (P : Nat) : Nat :=
  matOfK NSP NIP (fun c => spanA.getD c 0) (fun c => spanB.getD c 0) P

@[expose] noncomputable def r127Wit (w : List Int × Nat) (k : (Nat × Nat × Nat) → Bool) : Bool :=
  strictB (wO w.1) fun c => strictB (r127M c) fun C => strictB (r127M (pinv c)) fun D => k (C, D, w.2)

@[expose] noncomputable def r127Scan (b : Nat) : Bool :=
  strictB (ycK saCodes yIdxT) fun YP => strictB (tyLK YP r127Ty 2) fun L2 =>
  strictB (saAtK YP 10) fun X =>
  r127Wit (r127W.getD 0 ([], 0)) fun w0 => r127Wit (r127W.getD 1 ([], 0)) fun w1 =>
    allBlk b (scanAt saCodes saParT saLabT L2 X [w0, w1]) (nat_lit 1024)

@[expose] noncomputable def r127Pair : Bool :=
  strictB (ycK saCodes yIdxT) fun YP => strictB (tyLK YP r127Ty 1) fun L1 =>
  strictB (rootsK saCodes saParT saLabT L1) fun R => pairK saCodes YP R

theorem kScan127_0 : r127Scan 0 = true := by quickRfl
theorem kScan127_1 : r127Scan 1024 = true := by quickRfl
theorem kScan127_2 : r127Scan 2048 = true := by quickRfl
theorem kScan127_3 : r127Scan 3072 = true := by quickRfl
theorem kScan127_4 : r127Scan 4096 = true := by quickRfl
theorem kScan127_5 : r127Scan 5120 = true := by quickRfl
theorem kScan127_6 : r127Scan 6144 = true := by quickRfl
theorem kScan127_7 : r127Scan 7168 = true := by quickRfl

theorem kPair127 : r127Pair = true := by quickRfl

theorem kWit127 : List.all r127W (fun w => bAnd(lettersK 17 w.1, strictB (wO w.1) fun c =>
    bAnd(cn c, bAnd(pm c, bAnd(cn (pinv c),
    bAnd(Nat.beq (pc c (mainK 0)) (pc (mainK 0) c),
    bAnd(actsK NSP NIP c (r127M c), actsK NSP NIP (pinv c) (r127M (pinv c))))))))) = true := by
  quickRfl

theorem kRel127 : bAnd(Nat.beq (pc (AP.S 8) (pc (AP.S 8) (AP.S 8))) pid,
    bAnd(Nat.beq (pc (AP.S 9) (AP.S 9)) pid,
      Nat.beq (pc (pc (AP.S 9) (AP.S 8)) (AP.S 9)) (pc (AP.S 8) (AP.S 8)))) = true := by quickRfl

theorem kFix127 : allN 5 (fun t => Nat.beq (fix360K (mainK t)) (r127Fix.getD t 0)) = true := by
  quickRfl

theorem kCent127 : allN 5 (fun l => Nat.beq (pc (AP.S (sylowIdx.getD l 0)) (mainK 0))
    (pc (mainK 0) (AP.S (sylowIdx.getD l 0)))) = true := by quickRfl

end CertificateChecks.KernelO8

end
