module

public import Certificates.Kernel.Sporadic.OddCore.SuzFbM
public import Certificates.Kernel.Sporadic.OddCore.SuzFbP0
public import Certificates.Kernel.Sporadic.OddCore.SuzFbP1
public import Certificates.Kernel.Sporadic.OddCore.SuzFbP2
public import Certificates.Kernel.Sporadic.OddCore.SuzFbK0
public import Certificates.Kernel.Sporadic.OddCore.SuzFbK1
public import Certificates.Kernel.Sporadic.OddCore.SuzFbK2
public import Certificates.Kernel.Sporadic.OddCore.SuzFbK3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzFb.slPAll CertificateChecks.KernelSpor.SuzFb.slP 81
#kon_join CertificateChecks.KernelSpor.SuzFb.kindSlAll
  CertificateChecks.KernelSpor.SuzFb.kindSl 1216
#kon_join CertificateChecks.KernelSpor.SuzFb.invSlAll CertificateChecks.KernelSpor.SuzFb.invSl 16
#kon_join CertificateChecks.KernelSpor.SuzFb.liftSlAll CertificateChecks.KernelSpor.SuzFb.liftSl 13
#kon_join CertificateChecks.KernelSpor.SuzFb.qeSlAll CertificateChecks.KernelSpor.SuzFb.qeSl 26
#kon_join CertificateChecks.KernelSpor.SuzFb.conjNegAll
  CertificateChecks.KernelSpor.SuzFb.conjNeg 76

namespace CertificateChecks.KernelSpor.SuzFb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.PSL3Four.Native CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzMGF

theorem kSz : szOK 64 7 = true := by quickRfl

theorem kHd : penumHdK (pidn 64 7) SuzFbE.cnt 25920 SuzFbE.T SuzFbE.PL = true := by quickRfl

theorem kG : allN 10 (fun k => Nat.beq (SuzFbE.G k) (SuzABM k)) = true := by quickRfl

theorem kPar : allN 25920 (fun i => bIf(Nat.beq i 0, true, Nat.blt (parOf SuzFbE.PL i) i)) =
    true := by quickRfl

theorem kWord : allN 76 wordOK = true := by quickRfl

theorem kConjPos : allN 76 conjPos = true := by quickRfl

theorem kW : wOK = true := by quickRfl

theorem kLen : SuzFbIL.length = 76 := by decide +kernel

theorem kSorted : SuzFbIL.Pairwise (· < ·) := by decide +kernel

theorem kBound : ∀ x ∈ SuzFbIL, x < 25920 := by decide +kernel

theorem kCountW : (((List.range 76).map fun q =>
    countBelow 128 fun j => Nat.land (kE q j) 3 == 1).sum == 480) = true := by quickRfl

theorem kCountZ : (((List.range 76).map fun q => if (!(cw q == 0)) = true then
    countBelow 128 (fun j => Nat.land (kE q j) 3 == 2) else 0).sum == 1200) = true := by quickRfl

theorem negKind : Bool.not (kindOK (SuzFbL 2) 0 (Nat.xor (kE 2 0) 1)) = true := by quickRfl

theorem negInv : Bool.not (allN 1620 fun i =>
    bIf(fixInvK (SuzFbE.T i), memK SuzFbIL.tail i, Bool.not (memK SuzFbIL.tail i))) = true := by
  quickRfl

theorem negWord : Bool.not (Nat.beq (mWK (wq 3)) (SuzFbE.T (ipos 2))) = true := by quickRfl

theorem negLift : Bool.not (Nat.beq (SuzFbL 3) (cWK (wq 2))) = true := by quickRfl

theorem negCount : Bool.not (((List.range 76).map fun q =>
    countBelow 128 fun j => Nat.land (kE q j) 3 == 1).sum == 481) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzFb

end
