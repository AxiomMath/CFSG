module

public import Certificates.Kernel.HSStd.U43Z4Data
public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.U43Case
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelU43B CertificateChecks.KernelHSStd
open CFSG.LieType.Multipliers.U43

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 820 10 (mask 10) (820 * 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def TK (k : Nat) : Nat :=
  pc (ppw 820 10 (Z4P 10) (Nat.div k 4)) (ppw 820 10 (Z4P 11) (Nat.mod k 4))

@[expose] noncomputable def TKI (k : Nat) : Nat := pinvS 820 10 (mask 10) (TK k)

@[expose] noncomputable def cosK (i : Nat) : Bool :=
  strictB (Z4K i) fun k => bAnd(Nat.blt k 4,
    siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 (pc (Z4P i) (TKI k)))

theorem kBind : bindListK 820 10 (Z4P 0) rep8.toList = true ∧
    bindListK 820 10 (Z4P 1) z4Y0.toList = true ∧
    bindListK 820 10 (Z4P 2) z4Cg[0]!.toList = true ∧
    bindListK 820 10 (Z4P 3) z4Cg[1]!.toList = true ∧
    bindListK 820 10 (Z4P 4) z4Cg[2]!.toList = true ∧
    bindListK 820 10 (Z4P 5) z4Cg[3]!.toList = true ∧
    bindListK 820 10 (Z4P 6) z4Yg[0]!.toList = true ∧
    bindListK 820 10 (Z4P 7) z4Yg[1]!.toList = true ∧
    bindListK 820 10 (Z4P 8) tabA.toList = true ∧
    bindListK 820 10 (Z4P 9) tabB.toList = true ∧
    bindListK 820 10 (Z4P 10) phiArr.toList = true ∧
    bindListK 820 10 (Z4P 11) deltaArr.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem kSz : (szOK 820 10 && cK (pidn 820 10) && CFSG.KS.Prim.idK 820 10 (mask 10) &&
    Nat.beq z4Cg.size 4 && Nat.beq z4Yg.size 2) = true := by
  quickRfl

theorem kIn : allN 12 (fun i => bAnd(cK (Z4P i), bAnd(cK (Z4I i),
    invEqK 820 10 (mask 10) (820 * 10) (Z4P i) (Z4I i)))) = true := by
  quickRfl

theorem kTK : allN 8 (fun k => bAnd(cK (TK k), permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k))) =
    true := by
  quickRfl

theorem kCos : allN 8 (fun i => cosK (Nat.add i 2)) = true := by quickRfl

theorem kCosT : siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0
    (pc (TK 1) (TKI 1)) = true := by
  quickRfl

theorem kComm : (allN 4 (fun j => commP 820 10 (Z4P (Nat.add j 2)) (Z4P 0)) &&
    allN 2 (fun j => commP 820 10 (Z4P (Nat.add j 6)) (Z4P 1))) = true := by
  quickRfl

theorem kHC : allN 4 (fun j => Nat.beq (Z4C.GI j) (Z4P (Nat.add j 2)) &&
    Nat.beq (Z4C.G j) (pidn 820 10)) = true := by quickRfl

theorem kHY : allN 2 (fun j => Nat.beq (Z4Y.GI j) (Z4P (Nat.add j 6)) &&
    Nat.beq (Z4Y.G j) (pidn 820 10)) = true := by quickRfl

@[expose] noncomputable def GG (j : Nat) : Nat := nIf(Nat.beq j 0, Z4P 8, nIf(Nat.beq j 1, Z4P 9, TK 1))

@[expose] noncomputable def GGI (j : Nat) : Nat :=
  nIf(Nat.beq j 0, Z4I 8, nIf(Nat.beq j 1, Z4I 9, TKI 1))

theorem kHT : allN 3 (fun j => Nat.beq (Z4KT.G j) (GG j) && Nat.beq (Z4KT.GI j) (GGI j) &&
    Nat.beq (Z4KY.G j) (GG j) && Nat.beq (Z4KY.GI j) (GGI j)) = true := by quickRfl

theorem kHCY : allN 4 (fun j => Nat.beq (Z4CY.G j) (Z4P (Nat.add j 2)) &&
    Nat.beq (Z4CY.GI j) (Z4I (Nat.add j 2))) = true := by quickRfl

theorem kCnt : (Nat.beq Z4C.cnt 2880 && Nat.beq Z4Y.cnt 1944 && Nat.beq Z4KT.cnt 4536 &&
    Nat.beq Z4KY.cnt 6720 && Nat.beq Z4CY.cnt 80) = true := by quickRfl

theorem kHd : (penumHdK (pidn 820 10) Z4C.cnt 50000 Z4C.T Z4C.PL &&
    penumHdK (pidn 820 10) Z4Y.cnt 50000 Z4Y.T Z4Y.PL &&
    penumHdK (Z4P 0) Z4KT.cnt 50000 Z4KT.T Z4KT.PL &&
    penumHdK (Z4P 1) Z4KY.cnt 50000 Z4KY.T Z4KY.PL &&
    penumHdK (Z4P 1) Z4CY.cnt 50000 Z4CY.T Z4CY.PL) = true := by quickRfl

theorem cyPe : penumSlK 820 10 (mask 10) (820 * 10) true Z4CY.G Z4CY.GI 4 Z4CY.cnt Z4CY.T
    Z4CY.PL Z4CY.POS Z4CY.SRT Z4CY.SRI 0 Z4CY.cnt = true := by quickRfl

theorem cyHs : slK Z4CY.cnt (hsortPtK 820 10 (mask 10) Z4CY.cnt Z4CY.T Z4CY.HS Z4CY.HSI)
    0 Z4CY.cnt = true := by quickRfl

end CertificateChecks.KernelHSStd.U43Z4

end
