module

public import Certificates.Kernel.SporSch.Ly.GenLy
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Const
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

set_option maxRecDepth 400000

#kly_bsdata CertificateChecks.KernelSporSch.LyBS

#ks_chars CertificateChecks.KernelSporSch.LySA CFSG.Sporadic.Ly.Native.seedA

#ks_chars CertificateChecks.KernelSporSch.LySB CFSG.Sporadic.Ly.Native.seedB

#ks_chars CertificateChecks.KernelSporSch.LyW0 CFSG.Sporadic.LySchreier.Native.seedWord0Txt

#ks_chars CertificateChecks.KernelSporSch.LyW1 CFSG.Sporadic.LySchreier.Native.seedWord1Txt

namespace CertificateChecks.KernelSporSch.LyBS

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy

@[expose] noncomputable def mul (X Y : Nat) : Nat := mulR 5 12 1332 111 8 L H CM RM X Y

@[expose] noncomputable def vld (X : Nat) : Bool := validM 5 147852 L H X

@[expose] noncomputable def GS (i : Nat) : Nat := nIf(Nat.beq i 0, A, B)

@[expose] noncomputable def GSI (i : Nat) : Nat := nIf(Nat.beq i 0, A, B4)

@[expose] noncomputable def CFx (k i : Nat) : Nat := nIf(Nat.blt i k, CF i, ONE)

@[expose] noncomputable def CIx (k i : Nat) : Nat := nIf(Nat.blt i k, CI i, ONE)

@[expose] noncomputable def CZ (i : Nat) : Nat := nIf(Nat.blt i 12, CF i, A)

@[expose] noncomputable def CZI (i : Nat) : Nat := nIf(Nat.blt i 12, CI i, A)

@[expose] noncomputable def TSx (i : Nat) : Nat := nIf(Nat.blt i 10, TS i, ONE)

@[expose] noncomputable def TISx (i : Nat) : Nat :=
  nIf(Nat.blt i 9, mul (TS i) (TS i), nIf(Nat.beq i 9, A, ONE))

@[expose] noncomputable def TSs (i : Nat) : Nat := TSx (nIf(Nat.beq i 6, 7, nIf(Nat.beq i 7, 6, i)))

@[expose] noncomputable def TISs (i : Nat) : Nat := TISx (nIf(Nat.beq i 6, 7, nIf(Nat.beq i 7, 6, i)))

end CertificateChecks.KernelSporSch.LyBS

#kly_bschain CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBS.W0
  CertificateChecks.KernelSporSch.LyBS.GS CertificateChecks.KernelSporSch.LyBS.GSI K0 16

#kly_bschain CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBS.W1
  CertificateChecks.KernelSporSch.LyBS.GS CertificateChecks.KernelSporSch.LyBS.GSI K1 16

namespace CertificateChecks.KernelSporSch.LyBS

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native

theorem consts : constsOK 5 12 1332 111 8 L H CM RM ONE LV HV = true := by quickRfl

theorem payA : Nat.beq (payRunP 5 111 12 1332 LySA.chars 0 0 0) A = true := by quickRfl
theorem payB : Nat.beq (payRunP 5 111 12 1332 LySB.chars 0 0 0) B = true := by quickRfl
theorem vA : vld A = true := by quickRfl
theorem vB : vld B = true := by quickRfl
theorem vB4 : vld B4 = true := by quickRfl
theorem pB4 : Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE B 4) B4 = true := by quickRfl
theorem vCF : allN 12 (fun i => bAnd(vld (CF i), vld (CI i))) = true := by quickRfl
theorem iCF : allN 12 (fun i => Nat.beq (mul (CF i) (CI i)) ONE) = true := by quickRfl
theorem parse0 : parseK LyW0.chars W0 = true := by quickRfl
theorem parse1 : parseK LyW1.chars W1 = true := by quickRfl
theorem k00 : Nat.beq (K0 0) ONE = true := by quickRfl
theorem k10 : Nat.beq (K1 0) ONE = true := by quickRfl
theorem k0m : Nat.beq (K0 K0.m) (CF 0) = true := by quickRfl
theorem k1m : Nat.beq (K1 K1.m) (CF 1) = true := by quickRfl
theorem len0 : Nat.ble W0.length (Nat.mul K0.m 16) = true := by quickRfl
theorem len1 : Nat.ble W1.length (Nat.mul K1.m 16) = true := by quickRfl

theorem der : allN 10 (fun t => Nat.beq (wordR 5 12 1332 111 8 L H CM RM (CFx (Nat.add 2 t))
    (CIx (Nat.add 2 t)) ONE ((cDerivations ()).toList.getD t [])) (CF (Nat.add 2 t))) = true := by
  quickRfl

theorem u1 : Nat.beq (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE
    ((sylowWords ())[1]!)) U1 = true := by quickRfl
theorem u2 : Nat.beq (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE
    ((sylowWords ())[2]!)) U2 = true := by quickRfl
theorem vU : bAnd(vld U1, vld U2) = true := by quickRfl

theorem ts : allN 9 (fun i => Nat.beq (wordR 5 12 1332 111 8 L H CM RM CZ CZI ONE
    (bsTWordsN.getD i [])) (TS i)) = true := by quickRfl
theorem ts9 : Nat.beq (TS 9) A = true := by quickRfl
theorem vTS : allN 10 (fun i => vld (TS i)) = true := by quickRfl

theorem mf : Nat.beq (mul (mul (mul U2 U1) U2) U1) MF = true := by quickRfl
theorem hm : Nat.beq (mul (mul (mul A B) A) (mul B4 A)) HM = true := by quickRfl
theorem mg : Nat.beq (mul (powR 5 12 1332 111 8 L H CM RM ONE (mul HM MF) 7)
    (powR 5 12 1332 111 8 L H CM RM ONE (mul A HM) 4)) MG = true := by quickRfl
theorem vM : bAnd(vld MF, bAnd(vld HM, vld MG)) = true := by quickRfl

theorem cube : allN 9 (fun i => Nat.beq (mul (mul (TS i) (TS i)) (TS i)) ONE) = true := by quickRfl

theorem wf : Nat.beq (wordR 5 12 1332 111 8 L H CM RM TSx TISx ONE bsWfN) MF = true := by quickRfl
theorem gz : Nat.beq (mul MG A) (mul MF MG) = true := by quickRfl
theorem wm : Nat.beq (mul (wordR 5 12 1332 111 8 L H CM RM TSx TISx ONE bsWmN) MG)
    (mul MG (wordR 5 12 1332 111 8 L H CM RM TSx TISx ONE bsVN)) = true := by quickRfl
theorem ws : Nat.beq (mul (wordR 5 12 1332 111 8 L H CM RM TSs TISs ONE bsWmN) MG)
    (mul MG (wordR 5 12 1332 111 8 L H CM RM TSx TISx ONE bsUN)) = true := by quickRfl

end CertificateChecks.KernelSporSch.LyBS

end
