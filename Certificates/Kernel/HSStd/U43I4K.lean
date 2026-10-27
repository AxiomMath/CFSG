module

public import Certificates.Kernel.HSStd.U43I4Data
public import Certificates.Kernel.CU43Aut.Cls
public import Certificates.Data.Kernel.U43Wit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43I4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.CentBound CFSG.KC.U43Case CFSG.KC.U43Wit
open CertificateChecks.KernelCU43Aut

@[expose] noncomputable def inRK (g k : Nat) : Bool :=
  bAnd(Nat.blt k (nat_lit 8), inPK (pc g (I4TD k)))

@[expose] noncomputable def elOK (g g' k : Nat) : Bool :=
  bAnd(cK g, bAnd(cK g', bAnd(invEqK 820 10 (mask 10) (820 * 10) g g', inRK g k)))

@[expose] noncomputable def cmK (a b : Nat) : Bool := Nat.beq (pc a b) (pc b a)

@[expose] noncomputable def sQ (q : Nat) : Nat :=
  pc (ppw 820 10 (I4G 2) (Nat.mod (Nat.succ q) (nat_lit 3)))
    (ppw 820 10 (I4G 3) (Nat.div (Nat.succ q) (nat_lit 3)))

theorem kTD : allN 8 (fun k => Nat.beq (I4TD k) (TKI k)) = true := by quickRfl

theorem kU5 : bAnd(elOK (I4G 0) (I4GI 0) (I4GK 0),
    Nat.beq (pc (I4G 0) (CU43T 6)) (pc (CU43T 7) (I4G 0))) = true := by quickRfl

theorem kY0 : bAnd(elOK (I4G 1) (I4GI 1) (I4GK 1), bAnd(ord3P 820 10 (I4G 1),
    cmK (I4G 1) (CU43T 6))) = true := by quickRfl

theorem kS : bAnd(allN 2 (fun i => bAnd(elOK (I4G (Nat.add i 2)) (I4GI (Nat.add i 2))
      (I4GK (Nat.add i 2)), bAnd(ord3P 820 10 (I4G (Nat.add i 2)), cmK (I4G (Nat.add i 2)) (CU43T 6)))),
    bAnd(cmK (I4G 2) (I4G 3), bAnd(neB (I4G 3) (I4G 2), neB (I4G 3) (pc (I4G 2) (I4G 2))))) = true := by
  quickRfl

theorem kQ : allN 8 (fun q => bAnd(elOK (I4Q q) (I4QI q) (I4QK q), bAnd(cmK (I4Q q) (CU43T 6),
    Nat.beq (pc (I4Q q) (I4G 1)) (pc (sQ q) (I4Q q))))) = true := by quickRfl

theorem kH : allN 5 (fun l => bAnd(elOK (I4H l) (I4HI l) (I4HK l), cmK (I4H l) (CU43T 6))) = true := by
  quickRfl

theorem kTw : bAnd(towerK 820 10 (mask 10) I4H I4L 5 5,
    Nat.beq (towerProdK 10 (mask 10) I4L 5) 2880) = true := by quickRfl

theorem kUb : bAnd(cK (I4G 4), bAnd(cK (I4GI 4), bAnd(invEqK 820 10 (mask 10) (820 * 10) (I4G 4) (I4GI 4),
    bAnd(inPK (I4G 4), bAnd(cK (I4G 5), bAnd(cK (I4GI 5),
    bAnd(invEqK 820 10 (mask 10) (820 * 10) (I4G 5) (I4GI 5),
    bAnd(Nat.beq (pc (I4G 5) (I4G 4)) (pc (I4G 4) (I4G 1)), ubOK (I4G 5) I4O 81)))))))) = true := by
  quickRfl

theorem kYG : allN 4 (fun j => bAnd(elOK (I4YG j) (I4YGI j) (I4YGK j), cmK (I4YG j) (I4G 1))) = true := by
  quickRfl

theorem kY0e : Nat.beq (I4Y 0) (pidn 820 10) = true := by quickRfl

theorem kTr0 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 0 81 = true := by quickRfl
theorem kTr1 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 81 81 = true := by quickRfl
theorem kTr2 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 162 81 = true := by quickRfl
theorem kTr3 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 243 81 = true := by quickRfl
theorem kTr4 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 324 81 = true := by quickRfl
theorem kTr5 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 405 81 = true := by quickRfl
theorem kTr6 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 486 81 = true := by quickRfl
theorem kTr7 : treeK 820 10 I4YG 4 I4Y I4YP I4YL 648 567 81 = true := by quickRfl

theorem kSort : sortK I4Y I4SG 648 = true := by quickRfl

theorem kNs0 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 0 81 = true := by quickRfl
theorem kNs1 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 81 81 = true := by quickRfl
theorem kNs2 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 162 81 = true := by quickRfl
theorem kNs3 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 243 81 = true := by quickRfl
theorem kNs4 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 324 81 = true := by quickRfl
theorem kNs5 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 405 81 = true := by quickRfl
theorem kNs6 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 486 81 = true := by quickRfl
theorem kNs7 : noSolK 820 10 (CU43T 6) (I4G 1) I4WC I4WK 648 I4Y 567 81 = true := by quickRfl

end CertificateChecks.KernelHSStd.U43I4

end
