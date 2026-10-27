module

public import Certificates.Kernel.LocalComp.Sp6J.Checks
public import Certificates.Data.Kernel.SporSch.SliceK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6J

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.EvenSmallLie.Sp6 CertificateChecks.KernelSpor

theorem negOrd : Nat.beq (ordK XQ.LR 6) 2903040 = false := by decide +kernel

theorem negRep : allN RX.N (repK 36 6 XQ.S XQ.SI 2 RX.CS RX.OFF RX.CI (fun j => RX.E (j + 1))
    RX.P RX.L RX.K RX.S RX.SI RX.N 4000) = false := by decide +kernel

theorem negTr : trOrbK 36 6 XQ.LR XQ.TR 0 0 = false := by decide +kernel

theorem negTrC : trOrbK 36 6 C1Q.LR C1Q.TR 0 1 = false := by decide +kernel

theorem negWord : Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI [1, 2]) (RX.E (lget RX.OFF 0)) =
    false := by decide +kernel

theorem negOrd2 : ordIs 36 6 (mask 6) (pidn 36 6) (RF1.E (lget RF1.OFF 0)) (2 - 1) = false := by
  decide +kernel

theorem negComm : allN 5 (fun j => commK 36 6 (mask 6) (36 * 6) (C1Q.S j) (RX.E (lget RX.OFF 1))) =
    false := by decide +kernel

theorem negSift : Co3Sp36.sift (pidn 36 6 - Nat.shiftLeft 1 6 + 1) = false := by decide +kernel

theorem negCnt : Nat.beq N1.CS.sum (RF1.N + 1) = false := by decide +kernel

end CertificateChecks.KernelLC.Sp6J

end
