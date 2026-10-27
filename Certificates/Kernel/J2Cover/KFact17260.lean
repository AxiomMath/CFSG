module

public import Certificates.Kernel.J2Cover.AutChain
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.J2Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFactNative
meta import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFactNative
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import Mathlib
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
meta import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
meta import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.KF17260

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact CFSG.PSL3Four.Native

meta def invM (t : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 t

meta def kfM : Array (Array Nat) := kf2Arrs
meta def kfiM : Array (Array Nat) := kf2Arrs.map invM
meta def repsM : Array (Array Nat) := invReps
meta def p3M : Array (Array Nat) := #[y0Arr, p3a, p3b, p3c]
meta def p3iM : Array (Array Nat) := p3M.map invM
meta def idM : Array Nat := idTab 315
meta def ids4M : Array (Array Nat) := Array.replicate 4 idM

meta def p3RecM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM p3M[j]! t) 4 idM 100).tabs

meta def p3ClM : Array (Array Nat) :=
  (p3RecM.map fun x => (p3M ++ p3iM).map fun g => comp 315 x g).flatten

end CertificateChecks.KernelJ2Cover.KF17260

#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.KF CertificateChecks.KernelJ2Cover.KF17260.kfM 9
#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.KFI CertificateChecks.KernelJ2Cover.KF17260.kfiM 9
#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.RP CertificateChecks.KernelJ2Cover.KF17260.repsM 9
#kmisc_packarrs CertificateChecks.KernelJ2Cover.KF17260.P3I CertificateChecks.KernelJ2Cover.KF17260.p3iM 9

#kmulh CertificateChecks.KernelJ2Cover.KF17260.P3 315 9 CertificateChecks.KernelJ2Cover.KF17260.ids4M
  CertificateChecks.KernelJ2Cover.KF17260.p3M CertificateChecks.KernelJ2Cover.KF17260.idM 100

#kfind CertificateChecks.KernelJ2Cover.KF17260.P3Cl CertificateChecks.KernelJ2Cover.KF17260.p3RecM
  CertificateChecks.KernelJ2Cover.KF17260.p3ClM

namespace CertificateChecks.KernelJ2Cover.KF17260

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def cK (X : Nat) : Bool := canonK 315 9 (mask 9) (315 * 9) X

@[expose] noncomputable def sP (X : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight X (315 * 9)) 0,
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 X)

@[expose] noncomputable def eltK (X XI : Nat) : Bool :=
  bAnd(cK X, bAnd(cK XI, bAnd(invEqK 315 9 (mask 9) (315 * 9) X XI, sP X)))

theorem ch17260bind : bAnd(allN 3 (fun i => arrBind kf2Arrs[i]! 315 9 (KF i)),
    bAnd(allN 3 (fun i => arrBind invReps[i]! 315 9 (RP i)),
    allN 4 (fun j => arrBind p3List[j]! 315 9 (P3.GI j)))) = true := by
  quickRfl

@[expose] noncomputable def kf2K (i : Nat) : Bool :=
  bAnd(eltK (KF i) (KFI i), bAnd(cK (RP i),
    ordPK 315 9 4 (prodK 315 9 [pc (RP i) (pc (pc (KFI i) (RP i)) (KF i))])))

theorem ch17260kf2 : allN 3 kf2K = true := by
  quickRfl

theorem ch17260y0 : bAnd(Nat.beq (pc (P3.GI 0) (RP 1)) (pc (RP 1) (P3.GI 0)),
    ordPK 315 9 3 (prodK 315 9 [P3.GI 0])) = true := by
  quickRfl

@[expose] noncomputable def p3K (j : Nat) : Bool :=
  bAnd(eltK (P3.GI j) (P3I j), Nat.beq (pc (P3.GI j) (P3.GI 0)) (pc (P3.GI 0) (P3.GI j)))

theorem ch17260p3 : allN 4 p3K = true := by
  quickRfl

theorem ch17260rec : bAnd(szOK 315 9, bAnd(allN 4 (fun j => Nat.beq (P3.G j) (pidn 315 9)),
    bAnd(penumHdK (pidn 315 9) P3.cnt 100 P3.T P3.PL, Nat.beq P3.cnt 27))) = true := by
  quickRfl

theorem ch17260pe : penumSlK 315 9 (mask 9) (315 * 9) true P3.G P3.GI 4 P3.cnt P3.T P3.PL P3.POS
    P3.SRT P3.SRI 0 P3.cnt = true := by
  quickRfl

theorem ch17260hs : slK P3.cnt (hsortPtK 315 9 (mask 9) P3.cnt P3.T P3.HS P3.HSI) 0 P3.cnt =
    true := by
  quickRfl

theorem ch17260cl : slK (Nat.mul P3.cnt 8)
    (findPtK P3.cnt P3.T (prodQK 315 9 (mask 9) 8 P3.T (bothK 4 P3.GI P3I)) P3Cl) 0
    (Nat.mul P3.cnt 8) = true := by
  quickRfl

theorem ch17260nc : bIf(Nat.beq (pc (P3.GI 1) (P3.GI 3)) (pc (P3.GI 3) (P3.GI 1)), false, true) =
    true := by
  quickRfl

theorem ch17260neg : bAnd(bIf(ordPK 315 9 2 (prodK 315 9 [P3.GI 0]), false, true),
    bAnd(bIf(Nat.beq P3.cnt 26, false, true),
    bAnd(bIf(ordPK 315 9 2 (prodK 315 9 [pc (RP 0) (pc (pc (KFI 0) (RP 0)) (KF 0))]), false, true),
    bIf(Nat.beq (pc (P3.GI 1) (P3.GI 3)) (pc (P3.GI 3) (P3.GI 1)), false, true)))) = true := by
  quickRfl

end CertificateChecks.KernelJ2Cover.KF17260

end
