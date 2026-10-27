module

public import Certificates.Kernel.EvenBN.K27586D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN.NLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open Certificates.TitsAschbacherNLocal

theorem f4 : (List.range 32).all (fun m => m % 8 == 0 || kWords.any fun w =>
    !Nat.beq (pc (FL.getD m 0) (wP V w)) (pc (wP V w) (FL.getD m 0))) = true := by quickRfl

theorem f5 : (List.range 32).all (fun m => m % 4 == 0 || kWords.any fun w =>
    !uL.any fun u => Nat.beq (pc (FL.getD m 0) (wP V w))
      (pc (pc (FL.getD u 0) (wP V w)) (FL.getD m 0))) = true := by quickRfl

theorem f7 : (List.range 32).all (fun m => m % 4 == 0 || !(List.range 8).any fun i =>
    Nat.beq (pc Y (FL.getD m 0)) (pc (pc (FL.getD (4 * i) 0) (FL.getD m 0)) Y)) = true := by
  quickRfl

end CertificateChecks.KernelEvenBN.NLoc

end
