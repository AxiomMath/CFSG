module

public import Certificates.Kernel.J2Cover.KFact17260
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J2Inputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J2Inputs
meta import Certificates.Kernel.J2Cover.KFact17260
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2HypOne

open CFSG.EvenSporadicStandard.HypOne.J2

meta def eM : Array (Array Nat) :=
  #[arrE1, arrE2, arrE3, arrL, CFSG.ComponentClassification.J2Cover.outerArr]
meta def eiM : Array (Array Nat) := eM.map CertificateChecks.KernelJ2Cover.KF17260.invM

end CertificateChecks.KernelJ2HypOne

#kmisc_packarrs CertificateChecks.KernelJ2HypOne.E CertificateChecks.KernelJ2HypOne.eM 9
#kmisc_packarrs CertificateChecks.KernelJ2HypOne.EI CertificateChecks.KernelJ2HypOne.eiM 9

namespace CertificateChecks.KernelJ2HypOne

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.J2Cover
open CertificateChecks.KernelJ2Cover.KF17260 CFSG.EvenSporadicStandard.HypOne.J2

@[expose] noncomputable def ord2K (X : Nat) : Bool := ordPK 315 9 2 (prodK 315 9 [X])

@[expose] noncomputable def commK24273 (X Y : Nat) : Bool := Nat.beq (pc X Y) (pc Y X)

@[expose] noncomputable def e8K : Bool :=
  bAnd(commK24273 (E 0) (E 1), bAnd(commK24273 (E 0) (E 2), bAnd(commK24273 (E 1) (E 2),
  bAnd(ord2K (E 0), bAnd(ord2K (E 1), bAnd(ord2K (E 2), bAnd(ord2K (pc (E 0) (E 1)),
  bAnd(ord2K (pc (E 0) (E 2)), bAnd(ord2K (pc (E 1) (E 2)), ord2K (pc (pc (E 0) (E 1)) (E 2)))))))))))

theorem ch24273bind : bAnd(arrBind arrE1 315 9 (E 0), bAnd(arrBind arrE2 315 9 (E 1),
    bAnd(arrBind arrE3 315 9 (E 2), bAnd(arrBind arrL 315 9 (E 3),
      arrBind CFSG.ComponentClassification.J2Cover.outerArr 315 9 (E 4))))) = true := by
  quickRfl

theorem ch24273elt : allN 4 (fun i => eltK (E i) (EI i)) = true := by quickRfl

theorem ch24273u : cK (E 4) = true := by quickRfl

theorem ch24273e8 : e8K = true := by quickRfl

theorem ch24273four : ord2K (pc (pc (pc (E 3) (E 4)) (EI 3)) (E 4)) = true := by quickRfl

theorem ch24273neg_ord : bIf(ord2K (E 3), false, true) = true := by quickRfl

theorem ch24273neg_comm : bIf(commK24273 (E 0) (E 3), false, true) = true := by quickRfl

theorem ch24273neg_sift : bIf(sP (E 4), false, true) = true := by quickRfl

end CertificateChecks.KernelJ2HypOne
