module

public import Certificates.Kernel.HSStd.U43VbData
public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.U43Case
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelU43B CertificateChecks.KernelHSStd
open CFSG.LieType.Multipliers.U43

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 820 10 (mask 10) (820 * 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def TK (k : Nat) : Nat :=
  pc (ppw 820 10 (VbP 11) (Nat.div k 4)) (ppw 820 10 (VbP 12) (Nat.mod k 4))

@[expose] noncomputable def TKI (k : Nat) : Nat := pinvS 820 10 (mask 10) (TK k)

@[expose] noncomputable def cosK (i : Nat) : Bool :=
  strictB (VbK i) fun k => bAnd(Nat.beq k 0 || Nat.beq k 2 || Nat.beq k 5 || Nat.beq k 7,
    siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 (pc (VbP i) (TKI k)))

theorem kBind : bindListK 820 10 (VbP 0) rep8.toList = true ∧
    bindListK 820 10 (VbP 1) vbY0.toList = true ∧
    bindListK 820 10 (VbP 2) vbCg[0]!.toList = true ∧
    bindListK 820 10 (VbP 3) vbCg[1]!.toList = true ∧
    bindListK 820 10 (VbP 4) vbCg[2]!.toList = true ∧
    bindListK 820 10 (VbP 5) vbCg[3]!.toList = true ∧
    bindListK 820 10 (VbP 6) vbCg[4]!.toList = true ∧
    bindListK 820 10 (VbP 7) vbYg[0]!.toList = true ∧
    bindListK 820 10 (VbP 8) vbYg[1]!.toList = true ∧
    bindListK 820 10 (VbP 9) tabA.toList = true ∧
    bindListK 820 10 (VbP 10) tabB.toList = true ∧
    bindListK 820 10 (VbP 11) phiArr.toList = true ∧
    bindListK 820 10 (VbP 12) deltaArr.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem kSz : (szOK 820 10 && cK (pidn 820 10) && CFSG.KS.Prim.idK 820 10 (mask 10) &&
    Nat.beq vbCg.size 5 && Nat.beq vbYg.size 2) = true := by
  quickRfl

theorem kIn : allN 13 (fun i => bAnd(cK (VbP i), bAnd(cK (VbI i),
    invEqK 820 10 (mask 10) (820 * 10) (VbP i) (VbI i)))) = true := by
  quickRfl

theorem kTK : allN 8 (fun k => bAnd(cK (TK k), permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k))) =
    true := by
  quickRfl

theorem kCos : allN 9 (fun i => cosK (Nat.add i 2)) = true := by quickRfl

theorem kCosT : (siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0
    (pc (TK 2) (TKI 2)) && siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0
    (pc (TK 5) (TKI 5))) = true := by
  quickRfl

theorem kComm : (allN 5 (fun j => commP 820 10 (VbP (Nat.add j 2)) (VbP 0)) &&
    allN 2 (fun j => commP 820 10 (VbP (Nat.add j 7)) (VbP 1))) = true := by
  quickRfl

theorem kHC : allN 5 (fun j => Nat.beq (VbC.GI j) (VbP (Nat.add j 2)) &&
    Nat.beq (VbC.G j) (pidn 820 10)) = true := by quickRfl

theorem kHY : allN 2 (fun j => Nat.beq (VbY.GI j) (VbP (Nat.add j 7)) &&
    Nat.beq (VbY.G j) (pidn 820 10)) = true := by quickRfl

@[expose] noncomputable def GG (j : Nat) : Nat :=
  nIf(Nat.beq j 0, VbP 9, nIf(Nat.beq j 1, VbP 10, nIf(Nat.beq j 2, TK 2, TK 5)))

@[expose] noncomputable def GGI (j : Nat) : Nat :=
  nIf(Nat.beq j 0, VbI 9, nIf(Nat.beq j 1, VbI 10, nIf(Nat.beq j 2, TKI 2, TKI 5)))

theorem kHT : allN 4 (fun j => Nat.beq (VbKT.G j) (GG j) && Nat.beq (VbKT.GI j) (GGI j) &&
    Nat.beq (VbKY.G j) (GG j) && Nat.beq (VbKY.GI j) (GGI j)) = true := by quickRfl

theorem kHCY : allN 5 (fun j => Nat.beq (VbCY.G j) (VbP (Nat.add j 2)) &&
    Nat.beq (VbCY.GI j) (VbI (Nat.add j 2))) = true := by quickRfl

theorem kCnt : (Nat.beq VbC.cnt 2880 && Nat.beq VbY.cnt 1944 && Nat.beq VbKT.cnt 4536 &&
    Nat.beq VbKY.cnt 6720 && Nat.beq VbCY.cnt 80) = true := by quickRfl

theorem kHd : (penumHdK (pidn 820 10) VbC.cnt 50000 VbC.T VbC.PL &&
    penumHdK (pidn 820 10) VbY.cnt 50000 VbY.T VbY.PL &&
    penumHdK (VbP 0) VbKT.cnt 50000 VbKT.T VbKT.PL &&
    penumHdK (VbP 1) VbKY.cnt 50000 VbKY.T VbKY.PL &&
    penumHdK (VbP 1) VbCY.cnt 50000 VbCY.T VbCY.PL) = true := by quickRfl

theorem cyPe : penumSlK 820 10 (mask 10) (820 * 10) true VbCY.G VbCY.GI 5 VbCY.cnt VbCY.T
    VbCY.PL VbCY.POS VbCY.SRT VbCY.SRI 0 VbCY.cnt = true := by quickRfl

theorem cyHs : slK VbCY.cnt (hsortPtK 820 10 (mask 10) VbCY.cnt VbCY.T VbCY.HS VbCY.HSI)
    0 VbCY.cnt = true := by quickRfl

end CertificateChecks.KernelHSStd.U43Vb

end
