module

public import Certificates.Kernel.J2Cover.KFact17260
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2InvertsGenNative
meta import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2InvertsGenNative
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
meta import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
meta import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.KF17260

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

meta def ivgXM : Array (Array Nat) := ivgX
meta def ivgXiM : Array (Array Nat) := ivgX.map invM
meta def ivgKM : Array (Array Nat) := ivgK
meta def ivgKiM : Array (Array Nat) := ivgK.map invM

end CertificateChecks.KernelJ2Cover.KF17260

#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.IX CertificateChecks.KernelJ2Cover.KF17260.ivgXM 9
#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.IXI CertificateChecks.KernelJ2Cover.KF17260.ivgXiM 9
#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.IK CertificateChecks.KernelJ2Cover.KF17260.ivgKM 9
#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.IKI CertificateChecks.KernelJ2Cover.KF17260.ivgKiM 9

namespace CertificateChecks.KernelJ2Cover.KF17260

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

@[expose] noncomputable def yK (i : Nat) : Nat := pc (IXI i) (pc (RP i) (pc (IX i) (RP i)))

@[expose] noncomputable def y2K (i : Nat) : Nat := pc (IK i) (pc (yK i) (IKI i))

@[expose] noncomputable def letK (i j : Nat) : Nat := nIf(Nat.beq j 0, yK i, y2K i)

@[expose] noncomputable def ivgKc (i : Nat) : Bool :=
  bAnd(arrBind ivgX[i]! 315 9 (IX i), bAnd(arrBind ivgK[i]! 315 9 (IK i),
  bAnd(eltK (IX i) (IXI i), bAnd(eltK (IK i) (IKI i), bAnd(cK (RP i), bAnd(cK (IKI i),
  bAnd(sP (yK i), bAnd(ordPK 315 9 ivgOrd[i]! (prodK 315 9 [yK i]),
  bAnd(ivgWA[i]!.all (· < 2), bAnd(ivgWB[i]!.all (· < 2),
  bAnd(Nat.beq (wfoldK 315 9 (mask 9) (letK i) ivgWA[i]! (pidn 315 9)) (PA.S 0),
    Nat.beq (wfoldK 315 9 (mask 9) (letK i) ivgWB[i]! (pidn 315 9)) (PA.S 1))))))))))))

theorem ch17264ivg : allN 3 ivgKc = true := by
  quickRfl

theorem ch17264base : bAnd(szOK 315 9, bAnd(cK (pidn 315 9), bAnd(cK (PA.S 0), cK (PA.S 1)))) =
    true := by
  quickRfl

theorem ch17264neg : bAnd(bIf(ordPK 315 9 6 (prodK 315 9 [yK 0]), false, true),
    bIf(Nat.beq (wfoldK 315 9 (mask 9) (letK 0) ivgWA[0]! (pidn 315 9)) (PA.S 1), false, true)) =
    true := by
  quickRfl

end CertificateChecks.KernelJ2Cover.KF17260

end
