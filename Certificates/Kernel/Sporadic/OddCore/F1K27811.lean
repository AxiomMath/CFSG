module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.PkPow
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYCheck
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.TS16J2T CFSG.EvenSporadicStandard.Fin76b.S16.j2Hex

#kmisc_hexflat CertificateChecks.KernelSpor.TS16J2T CFSG.EvenSporadicStandard.Fin76b.S16.j2Hex
  3 315 9 14

#ks_chars CertificateChecks.KernelSpor.TS16J3T CFSG.EvenSporadicStandard.Fin76b.S16.j3Hex

#kmisc_hexflat CertificateChecks.KernelSpor.TS16J3T CFSG.EvenSporadicStandard.Fin76b.S16.j3Hex
  4 513 13 156

namespace CertificateChecks.KernelSpor.F27811

open CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.Sporadic.SmallOddCore.Native

meta def j3TsM : Array (Array Nat) := (List.range 13).toArray.map fun k => natArr (j3Tb k)

end CertificateChecks.KernelSpor.F27811

#kmisc_packarrs CertificateChecks.KernelSpor.TS16J3P CertificateChecks.KernelSpor.F27811.j3TsM 13

namespace CertificateChecks.KernelSpor.F27811

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Join CFSG.KC.PkPow
open CertificateChecks.KernelSporSch

theorem ts16_join : joinK 12 (13 * 513) TS16J3T.F TS16J3P 13 = true := by
  quickRfl

@[expose] noncomputable def f1K (n w t r u : Nat) (sr su : Bool) : Bool :=
  strictB (ppw n w r 7) fun ri =>
  bAnd(szOK n w, bAnd(canonK n w (mask w) (n * w) (pidn n w),
  bAnd(canonK n w (mask w) (n * w) t, bAnd(canonK n w (mask w) (n * w) r,
  bAnd(canonK n w (mask w) (n * w) u, bAnd(canonK n w (mask w) (n * w) ri,
  bAnd(invEqK n w (mask w) (n * w) r ri, bAnd(invEqK n w (mask w) (n * w) u u,
  bAnd(sr, bAnd(su,
  bAnd(Nat.beq (pcomp n w (mask w) r t) (pcomp n w (mask w) t r),
  bAnd(Nat.beq (pcomp n w (mask w) u t) (pcomp n w (mask w) t u),
  bAnd(Nat.beq (ppw n w r 8) (pidn n w), bAnd(bIf(Nat.beq (ppw n w r 4) (pidn n w), false, true),
  bAnd(Nat.beq (pcomp n w (mask w) u u) (pidn n w),
  bAnd(Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) u r) u) ri,
    (List.range 8).all fun i => !Nat.beq u (ppw n w r i)))))))))))))))))

@[expose] def rWord : List Int := [3, 2, 3, 2, 4, 3, 2, 3, 1, 3, 4, 5, 1, 4, 5, 5]

@[expose] def uWord : List Int := [2, 2, 3, 2, 1, 2, 1, 2, 4, 3, 3, 1, 5]

@[expose] noncomputable def j3W (wd : List Int) (p : Nat) : Bool :=
  wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 wd p

theorem k27811_j2 : f1K 315 9 (J2Cn.F 9) (TS16J2T.F 12) (TS16J2T.F 13)
    (J2Cn.sK (TS16J2T.F 12)) (J2Cn.sK (TS16J2T.F 13)) = true := by
  quickRfl

theorem k27811_j3 : f1K 6156 13 (J3CentP 21) (TS16J3P 11) (TS16J3P 12)
    (j3W rWord (TS16J3P 11)) (j3W uWord (TS16J3P 12)) = true := by
  quickRfl

theorem k27811_j2_neg : f1K 315 9 (J2Cn.F 9) (ppw 315 9 (TS16J2T.F 12) 2) (TS16J2T.F 13)
    true true = false := by
  decide +kernel

theorem k27811_j3_neg : f1K 6156 13 (J3CentP 21) (ppw 6156 13 (TS16J3P 11) 2) (TS16J3P 12)
    true true = false := by
  decide +kernel

end CertificateChecks.KernelSpor.F27811

end
